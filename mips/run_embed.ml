(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Printf ;;
open Big_int_Z ;;
open Sail_values;;
open Mips_extras_ml;;

let interact_print = ref true
let result_print = ref true
let error_print = ref true
let interactf : ('a, out_channel, unit) format -> 'a =
  function f -> if !interact_print then printf f else ifprintf stderr f
let errorf : ('a, out_channel, unit) format -> 'a =
  function f -> if !error_print then printf f else ifprintf stderr f
let resultf : ('a, out_channel, unit) format -> 'a =
  function f -> if !result_print then printf f else ifprintf stderr f

let rec foldli f acc ?(i=0) = function
  | [] -> acc
  | x::xs -> foldli f (f i acc x) ~i:(i+1) xs;;

let hex_to_big_int s = big_int_of_int64 (Int64.of_string s) ;;
let big_int_to_hex i = 
  (* annoyingly Uint64.to_string_hex prefixes the string with 0x UNLESS it is zero... *) 
  if i = zero_big_int then
    "0"
  else
    let s = Uint64.to_string_hex (Uint64.of_string (string_of_big_int i)) in
    let len = String.length s in
    String.sub s 2 (len - 2)

let big_int_to_hex64 i = 
  let hex = big_int_to_hex i in
  let len = String.length hex in
  if (len < 16) then
    (String.make (16-len) '0') ^ hex
  else
    hex

let input_buf = (ref [] : int list ref);;

let add_mem byte addr mem = begin
  assert(byte >= 0 && byte < 256);
  (*printf "MEM [%s] <- %x\n" (big_int_to_hex addr) byte;*)
  mem := Mem.add addr byte !mem
end

let max_cut_off = ref false
let max_instr = ref 0
let raw_file = ref ""
let raw_at   = ref ""
let elf_file = ref ""
let model_arg = ref "cheri"

let args = [
  ("--model", Arg.Set_string model_arg, "CPU model to use (mips, cheri, cheri128)");
  ("--file", Arg.Set_string elf_file, "filename of elf binary to load in memory");
  ("--max_instruction", Arg.Int (fun i -> max_cut_off := true; max_instr := i), "only run i instructions, then stop");
  ("--raw", Arg.Set_string raw_file, "filename of raw file to load in memory");
  ("--at", Arg.Set_string raw_at, "address to load raw file in memory");
  ("--trace", Arg.Set trace_writes, "trace all register writes"); (* trace_writes is in sail_values.ml *)
  ("--quiet", Arg.Clear interact_print, "suppress trace of PC");
]

module type ISA_model = sig
  type ast
  val init_model : unit -> unit
  val inc_nextPC : unit -> unit
  val get_pc  : unit -> big_int
  val translate_pc : unit -> big_int option
  val get_opcode : big_int -> value
  val decode : value -> ast option
  val execute : ast -> unit
  val is_halt : ast -> bool
  val print_results : unit -> unit
end

let rec debug_print_gprs gprs start stop =
  let gpr_val = vector_access gprs (big_int_of_int start) in
  let gpr_str = 
    if has_undef gpr_val then
      "uuuuuuuuuuuuuuuu"
    else
      big_int_to_hex64 (unsigned_big(gpr_val)) in
  resultf "DEBUG MIPS REG %.2d 0x%s\n" start gpr_str;
  if start < stop
  then debug_print_gprs gprs (start + 1) stop
  else ()

let cap_reg_to_string reg =
  "0b" ^ (String.sub (string_of_value reg) 9 257)

let rec debug_print_caps capregs start stop =
  let cap_val = vector_access capregs (big_int_of_int start) in
  let cap_str = cap_reg_to_string cap_val in
  resultf "DEBUG CAP REG %.2d %s\n" start cap_str;
  if start < stop
  then debug_print_caps capregs (start + 1) stop
  else ()

module MIPS_model : ISA_model = struct
  type ast = Mips_embed._ast

  let init_model () = 
    let start_addr = (to_vec_dec_big (big_int_of_int 64, hex_to_big_int "0x9000000040000000")) in
    set_register Mips_embed._nextPC start_addr;
    set_register_field_bit Mips_embed._CP0Status "BEV" Vone

  let inc_nextPC () = 
    set_register Mips_embed._inBranchDelay Mips_embed._branchPending;
    set_register Mips_embed._branchPending (to_vec_dec_int (1, 0));
    set_register Mips_embed._PC Mips_embed._nextPC;
    let inBranchDelay = unsigned_int(Mips_embed._inBranchDelay) in
    (match inBranchDelay with
    | 0 ->
       let pc_vaddr = unsigned_big(Mips_embed._PC) in
       let npc_addr = add_int_big_int 4 pc_vaddr in
       let npc_vec = to_vec_dec_big (big_int_of_int 64, npc_addr) in
       set_register Mips_embed._nextPC npc_vec;
    | 1 ->
       set_register Mips_embed._nextPC Mips_embed._delayedPC;
    | _ -> failwith "invalid value of inBranchDelay")

  let get_pc () = unsigned_big (Mips_embed._PC)

  let translate_pc () = 
    try
      Some (unsigned_big(Mips_embed._TranslatePC(Mips_embed._PC)))
    with Sail_exit -> None

  let get_opcode pc_a = Mips_embed._reverse_endianness(_MEMr (to_vec_dec_big (big_int_of_int 64, pc_a), big_int_of_int 4))

  let decode = Mips_embed._decode

  let execute = Mips_embed._execute
  let is_halt i = (i = Mips_embed.HCF)
  let print_results () =
    begin
      resultf "DEBUG MIPS PC 0x%s\n" (big_int_to_hex (unsigned_big Mips_embed._PC));
      debug_print_gprs Mips_embed._GPR 0 31;
    end
end

module CHERI_model : ISA_model = struct
  type ast = Cheri_embed._ast

  let init_model () = 
    let start_addr = (to_vec_dec_big (big_int_of_int 64, hex_to_big_int "0x9000000040000000")) in
    set_register Cheri_embed._nextPC start_addr;
    set_register_field_bit Cheri_embed._CP0Status "BEV" Vone;
    let initial_cap_val_int = big_int_of_string "0x100000000fffffffe00000000000000000000000000000000ffffffffffffffff" in
    let initial_cap_vec = to_vec_dec ((big_int_of_int 257), initial_cap_val_int) in 
    set_register Cheri_embed._PCC initial_cap_vec;
    set_register Cheri_embed._nextPCC initial_cap_vec;
    set_register Cheri_embed._delayedPCC initial_cap_vec;
    for i = 0 to 31 do
      set_register (vector_access_int Cheri_embed._CapRegs i) initial_cap_vec
    done

  let inc_nextPC () = 
    set_register Cheri_embed._inBranchDelay Cheri_embed._branchPending;
    set_register Cheri_embed._branchPending (to_vec_dec_int (1, 0));
    set_register Cheri_embed._PC Cheri_embed._nextPC;
    set_register Cheri_embed._PCC Cheri_embed._nextPCC;
    let inBranchDelay = unsigned_int(Cheri_embed._inBranchDelay) in
    (match inBranchDelay with
    | 0 ->
       let pc_vaddr = unsigned_big(Cheri_embed._PC) in
       let npc_addr = add_int_big_int 4 pc_vaddr in
       let npc_vec = to_vec_dec_big (big_int_of_int 64, npc_addr) in
       set_register Cheri_embed._nextPC npc_vec;
    | 1 ->
       begin
         set_register Cheri_embed._nextPC Cheri_embed._delayedPC;
         set_register Cheri_embed._nextPCC Cheri_embed._delayedPCC;
       end
    | _ -> failwith "invalid value of inBranchDelay")

  let get_pc () = unsigned_big (Cheri_embed._PC)

  let translate_pc () = 
    try
      Some (unsigned_big(Cheri_embed._TranslatePC(Cheri_embed._PC)))
    with Sail_exit -> None

  let get_opcode pc_a = Cheri_embed._reverse_endianness(_MEMr (to_vec_dec_big (big_int_of_int 64, pc_a), big_int_of_int 4))

  let decode = Cheri_embed._decode

  let execute = Cheri_embed._execute
  let is_halt i = (i = Cheri_embed.HCF)
  let print_results () =
    begin
      resultf "DEBUG MIPS PC 0x%s\n" (big_int_to_hex (unsigned_big Cheri_embed._PC));
      debug_print_gprs Cheri_embed._GPR 0 31;
      resultf "DEBUG CAP PCC %s\n" (cap_reg_to_string Cheri_embed._PCC);
      debug_print_caps Cheri_embed._CapRegs 0 31;
    end 

end

let time_it action arg =
  let start_time = Sys.time () in
  let ret = action arg in
  let finish_time = Sys.time () in
  (finish_time -. start_time, ret)

let rec fde_loop (model, count) =
  if !max_cut_off && count = !max_instr
  then begin
      resultf "\nEnding evaluation due to reaching cut off point of %d instructions\n" count;
      count
    end
  else 
    begin
    let module Model = (val model : ISA_model) in
    Model.inc_nextPC ();
    if !interact_print then
      interactf "\n**** instruction %d from address %s ****\n"
                count (big_int_to_hex64 (Model.get_pc ()));
    let m_paddr = Model.translate_pc () in
    match m_paddr with
      | Some pc ->
          let opcode = Model.get_opcode pc in
          if !interact_print then
            interactf "decode: 0x%x\n" (unsigned_int(opcode));
          let instruction = Model.decode opcode in
          let i = match instruction with
            | Some (i) -> i
            | _ ->  begin
                errorf "\n**** Decode error ****\n"; 
                exit 1;
              end
          in
          if Model.is_halt i then 
            begin
              Model.print_results ();
              resultf "\nSUCCESS program terminated after %d instructions\n" count;
              count
            end
          else
            begin
              (try
                Model.execute(i)
              with Sail_exit -> ()); (* exception during execute *)
              fde_loop (model, count + 1)
            end
      | None -> (* Exception during PC translation *)
          fde_loop (model, count + 1)
  end

 (*
 (try
   let (pending, _, _)  = (Unix.select [(Unix.stdin)] [] [] 0.0) in
   (if (pending != []) then
     let char = (input_byte stdin) in (
     errorf "Input %x\n" char;
     input_buf := (!input_buf) @ [char]));
 with
 | _ -> ());

 let uart_rvalid = option_int_of_reg "UART_RVALID" in
 (match uart_rvalid with
 | Some 0 ->
   (match !input_buf with
   | x :: xs -> (
       reg := Reg.add "UART_RDATA" (register_value_of_integer 8 7 Sail_impl_base.D_decreasing (Nat_big_num.of_int x)) !reg;
       reg := Reg.add "UART_RVALID" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing (Nat_big_num.of_int 1)) !reg;
       input_buf := xs;
     )
   | [] -> ())
 | _-> ());

 let uart_written = option_int_of_reg "UART_WRITTEN" in
 (match uart_written with 
 | Some 1 ->
   (let uart_data = option_int_of_reg "UART_WDATA" in
   match uart_data with
   | Some b -> (printf "%c" (Char.chr b); printf "%!")
   | None   -> (errorf "UART_WDATA was undef" ; exit 1))
 | _      -> ());
 reg := Reg.add "UART_WRITTEN" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero) !reg;*)

let rec load_raw_file' mem addr chan =
  let byte = input_byte chan in
  (add_mem byte addr mem;
  load_raw_file' mem (Big_int_Z.add_int_big_int 1 addr) chan)

let rec load_raw_file mem addr chan =
  try 
    load_raw_file' mem addr chan
   with
  | End_of_file -> ()


let get_model = function
  | "cheri" -> (module CHERI_model : ISA_model)
  | "mips" -> (module MIPS_model : ISA_model)
  | _ -> failwith "unknown model name"

let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "" ;

  if String.length(!raw_file) != 0 then
    load_raw_file mips_mem (big_int_of_string !raw_at) (open_in_bin !raw_file);

  let name = Filename.basename !raw_file in
  let model = get_model !model_arg in
  let module Model = (val model  : ISA_model) in
  Model.init_model ();
  let (t, count) = time_it fde_loop (model, 0) in
  resultf "Execution time for file %s: %f seconds %f IPS \n" name t (float(count) /. t);;



(* Turn off line-buffering of standard input to allow responsive console input 
if Unix.isatty (Unix.stdin) then begin
  let tattrs = Unix.tcgetattr (Unix.stdin) in
  Unix.tcsetattr (Unix.stdin) (Unix.TCSANOW) ({tattrs with c_icanon=false})
end ;;
*)

run () ;;

