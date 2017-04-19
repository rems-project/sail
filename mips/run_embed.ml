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
(* The linksem ELF interface *)
open Sail_interface ;;

module Mips_model=Mips_embed;;

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

let args = [
  ("--file", Arg.Set_string elf_file, "filename of elf binary to load in memory");
  ("--max_instruction", Arg.Int (fun i -> max_cut_off := true; max_instr := i), "only run i instructions, then stop");
  ("--raw", Arg.Set_string raw_file, "filename of raw file to load in memory");
  ("--at", Arg.Set_string raw_at, "address to load raw file in memory");
]

let time_it action arg =
  let start_time = Sys.time () in
  let ret = action arg in
  let finish_time = Sys.time () in
  (finish_time -. start_time, ret)

let rec debug_print_gprs start stop =
  let gpr_val = vector_access Mips_model._GPR (big_int_of_int start) in
  let gpr_str = 
    if has_undef gpr_val then
      "uuuuuuuuuuuuuuuu"
    else
      big_int_to_hex64 (unsigned_big(gpr_val)) in
  resultf "DEBUG MIPS REG %.2d 0x%s\n" start gpr_str;
  if start < stop
  then debug_print_gprs (start + 1) stop
  else ()

let get_opcode pc_a = Mips_model._reverse_endianness(_MEMr (to_vec_dec_big (big_int_of_int 64, pc_a), big_int_of_int 4))

let get_pc () = begin
    try
      Some (unsigned_big(Mips_model._TranslatePC(Mips_model._PC)))
    with Sail_exit -> None
  end


let rec fde_loop count =
  if !max_cut_off && count = !max_instr
  then begin
      resultf "\nEnding evaluation due to reaching cut off point of %d instructions\n" count;
      count
    end
  else begin
    let pc_vaddr = unsigned_big(Mips_model._PC) in
    interactf "\n**** instruction %d from address %s ****\n"
      count (big_int_to_hex64 pc_vaddr);
    let m_paddr = get_pc () in
    match m_paddr with
      | Some pc ->
          let inBranchDelay = Some(unsigned_int(Mips_model._inBranchDelay)) in
          (match inBranchDelay with
          | Some 0 -> 
            let npc_addr = add_int_big_int 4 pc_vaddr in
            let npc_vec = to_vec_dec_big (big_int_of_int 64, npc_addr) in
            set_register Mips_model._nextPC npc_vec;
          | Some 1 ->
            set_register Mips_model._nextPC Mips_model._delayedPC;
          | _ -> failwith "invalid value of inBranchDelay");
          let opcode = get_opcode pc in
          let _ = resultf "decode: 0x%x\n" (unsigned_int(opcode)) in
          let instruction = Mips_model._decode opcode in
          let i = match instruction with
            | Some (i) -> i
            | _ ->  begin
                errorf "\n**** Decode error ****\n"; 
                exit 1;
              end
          in
          if (i == Mips_model.HCF)
          then 
            begin
              resultf "DEBUG MIPS PC 0x%s\n" (big_int_to_hex pc_vaddr);
              debug_print_gprs 0 31;
              resultf "\nSUCCESS program terminated after %d instructions\n" count;
              count
            end 
          else
            begin
              (try
                Mips_model._execute(i)
              with Sail_exit -> ());
              set_register Mips_model._inBranchDelay Mips_model._branchPending;
              set_register Mips_model._branchPending (to_vec_dec_int (1, 0));
              set_register Mips_model._PC Mips_model._nextPC;
              fde_loop (count + 1)
            end
      | None -> begin (* Exception during PC translation *)
          set_register Mips_model._inBranchDelay Mips_model._branchPending;
          set_register Mips_model._branchPending (to_vec_dec_int (1, 0));
          set_register Mips_model._PC Mips_model._nextPC;
          fde_loop (count + 1)
        end
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


let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "" ;
  (*if !elf_file = "" then begin
    Arg.usage args "";
    exit 1;
  end;*)
(*
  let ((isa_defs,
       (isa_m0, isa_m1, isa_m2, isa_m3,isa_m4),
        isa_externs,
        isa_model,
        model_reg_d,
        startaddr,
        startaddr_internal), pp_symbol_map) = initial_system_state_of_elf_file !file in
 *)
  if String.length(!raw_file) != 0 then
    load_raw_file mips_mem (big_int_of_string !raw_at) (open_in_bin !raw_file);
  set_register_field_bit Mips_model._CP0Status "BEV" Vone;
  let start_addr = (to_vec_dec_big (big_int_of_int 64, hex_to_big_int "0x9000000040000000")) in
  set_register Mips_model._PC start_addr;
  let name = Filename.basename !raw_file in
  let (t, count) = time_it fde_loop 0 in
  resultf "Execution time for file %s: %f seconds %f IPS \n" name t (float(count) /. t);;

(* Turn off line-buffering of standard input to allow responsive console input 
if Unix.isatty (Unix.stdin) then begin
  let tattrs = Unix.tcgetattr (Unix.stdin) in
  Unix.tcsetattr (Unix.stdin) (Unix.TCSANOW) ({tattrs with c_icanon=false})
end ;;
*)

run () ;;

