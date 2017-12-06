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

let big_int_to_hex i = Z.format "%x" i
let big_int_to_hex64 i = Z.format "%016x" i

let input_buf = (ref [] : int list ref);;

let max_cut_off = ref false
let max_instr = ref 0
let model_arg = ref "cheri"
let raw_list = ref []

let args = [
  ("--model", Arg.Set_string model_arg, "CPU model to use (mips, cheri, cheri128)");
  ("--max_instruction", Arg.Int (fun i -> max_cut_off := true; max_instr := i), "only run i instructions, then stop");
  ("--trace", Arg.Set trace_writes, "trace all register writes"); (* trace_writes is in sail_values.ml *)
  ("--quiet", Arg.Clear interact_print, "suppress trace of PC");
  ("--undef", Arg.String (fun s -> undef_val := bit_of_string s), "value to use for undef (u,0,1)");
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
  "0b" ^ (string_of_bit_array (get_barray reg))

let read_bit_reg = function
  | Vregister (array,_,_,_,_) -> (!array).(0) = Vone
  | _ -> failwith "read_bit_reg of non-reg"

let rec debug_print_caps capregs start stop =
  let cap_val = vector_access capregs (big_int_of_int start) in
  let cap_str = cap_reg_to_string cap_val in
  resultf "DEBUG CAP REG %.2d %s\n" start cap_str;
  if start < stop
  then debug_print_caps capregs (start + 1) stop
  else ()

let handle_uart uart_written uart_wdata uart_rdata uart_rvalid =
  (try
    let (pending, _, _) = Unix.select [Unix.stdin] [] [] 0.0 in
    if pending != [] then
      input_buf := (!input_buf) @ [(input_byte stdin)]
  with _ -> ());

  if (read_bit_reg uart_written) then
    begin
      let b = unsigned_int(uart_wdata) in
      printf "%c" (Char.chr b);
      printf "%!";
      set_register uart_written (to_vec_dec_int (1,0))
    end;
  
  if not (read_bit_reg uart_rvalid) then
    (match !input_buf with
     | x :: xs -> 
        begin
          set_register uart_rdata (to_vec_dec_int (8, x));
          set_register uart_rvalid (to_vec_dec_int (1, 1));
          input_buf := xs;
        end
     | _ -> ())

module MIPS_model : ISA_model = struct
  type ast = Mips_embed._ast

  let init_model () = 
    let start_addr = (to_vec_dec_big (bi64, big_int_of_string "0x9000000040000000")) in
    set_register Mips_embed._nextPC start_addr;
    set_register_field_bit Mips_embed._CP0Status "BEV" Vone

  let inc_nextPC () = 
    handle_uart Mips_embed._UART_WRITTEN Mips_embed._UART_WDATA Mips_embed._UART_RDATA Mips_embed._UART_RVALID;

    set_register Mips_embed._inBranchDelay Mips_embed._branchPending;
    set_register Mips_embed._branchPending (to_vec_dec_int (1, 0));
    set_register Mips_embed._PC Mips_embed._nextPC;
    let inBranchDelay = read_bit_reg Mips_embed._inBranchDelay in
    if inBranchDelay then
      set_register Mips_embed._nextPC Mips_embed._delayedPC
    else
      let pc_vaddr = unsigned_big(Mips_embed._PC) in
      let npc_addr = add_int_big_int 4 pc_vaddr in
      let npc_vec = to_vec_dec_big (bi64, npc_addr) in
      set_register Mips_embed._nextPC npc_vec

  let get_pc () = unsigned_big (Mips_embed._PC)

  let translate_pc () = 
    try
      Some (unsigned_big(Mips_embed._TranslatePC(Mips_embed._PC)))
    with Sail_exit -> None

  let get_opcode pc_a = Mips_embed._reverse_endianness(_MEMr (to_vec_dec_big (bi64, pc_a), bi4))

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
    let start_addr = (to_vec_dec_big (bi64, big_int_of_string "0x9000000040000000")) in
    set_register Cheri_embed._nextPC start_addr;
    set_register_field_bit Cheri_embed._CP0Status "BEV" Vone;
    let initial_cap_val_int = big_int_of_string "0x100000000fffffffe00000000000000000000000000000000ffffffffffffffff" in
    let initial_cap_vec = to_vec_dec ((big_int_of_int 257), initial_cap_val_int) in 
    set_register Cheri_embed._PCC initial_cap_vec;
    set_register Cheri_embed._nextPCC initial_cap_vec;
    set_register Cheri_embed._delayedPCC initial_cap_vec;
    cap_size_shift := 5; (* configure memory model cap_size in mips_extras_ml *)
    for i = 0 to 31 do
      set_register (vector_access_int Cheri_embed._CapRegs i) initial_cap_vec
    done

  let inc_nextPC () = 
    handle_uart Cheri_embed._UART_WRITTEN Cheri_embed._UART_WDATA Cheri_embed._UART_RDATA Cheri_embed._UART_RVALID;

    set_register Cheri_embed._inBranchDelay Cheri_embed._branchPending;
    set_register Cheri_embed._branchPending (to_vec_dec_int (1, 0));
    set_register Cheri_embed._PC Cheri_embed._nextPC;
    set_register Cheri_embed._PCC Cheri_embed._nextPCC;
    let inBranchDelay = read_bit_reg Cheri_embed._inBranchDelay in
    if inBranchDelay then
       begin
         set_register Cheri_embed._nextPC Cheri_embed._delayedPC;
         set_register Cheri_embed._nextPCC Cheri_embed._delayedPCC;
       end
    else
       let pc_vaddr = unsigned_big(Cheri_embed._PC) in
       let npc_addr = add_int_big_int 4 pc_vaddr in
       let npc_vec = to_vec_dec_big (bi64, npc_addr) in
       begin
         set_register Cheri_embed._nextPC npc_vec;
         set_register Cheri_embed._inCCallDelay (to_vec_dec_int (1, 0))
       end

  let get_pc () = unsigned_big (Cheri_embed._PC)

  let translate_pc () = 
    try
      Some (unsigned_big(Cheri_embed._TranslatePC(Cheri_embed._PC)))
    with Sail_exit -> None

  let get_opcode pc_a = Cheri_embed._reverse_endianness(_MEMr (to_vec_dec_big (bi64, pc_a), bi4))

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

module CHERI128_model : ISA_model = struct
  type ast = Cheri128_embed._ast

  let init_model () = 
    let start_addr = (to_vec_dec_big (bi64, big_int_of_string "0x9000000040000000")) in
    set_register Cheri128_embed._nextPC start_addr;
    set_register_field_bit Cheri128_embed._CP0Status "BEV" Vone;
    let initial_cap_val_int = big_int_of_string "0x1fffe6000000100000000000000000000" in (* hex((0x10000 << 64) + (48 << 105) + (0x7fff << 113) + (1 << 128)) T=0x10000 E=48 perms=0x7fff tag=1 *)
    let initial_cap_vec = to_vec_dec ((bi129), initial_cap_val_int) in 
    set_register Cheri128_embed._PCC initial_cap_vec;
    set_register Cheri128_embed._nextPCC initial_cap_vec;
    set_register Cheri128_embed._delayedPCC initial_cap_vec;
    cap_size_shift := 4; (* configure memory model cap_size in mips_extras_ml *)
    for i = 0 to 31 do
      set_register (vector_access_int Cheri128_embed._CapRegs i) initial_cap_vec
    done

  let inc_nextPC () = 
    handle_uart Cheri128_embed._UART_WRITTEN Cheri128_embed._UART_WDATA Cheri128_embed._UART_RDATA Cheri128_embed._UART_RVALID;

    set_register Cheri128_embed._inBranchDelay Cheri128_embed._branchPending;
    set_register Cheri128_embed._branchPending (to_vec_dec_int (1, 0));
    set_register Cheri128_embed._PC Cheri128_embed._nextPC;
    set_register Cheri128_embed._PCC Cheri128_embed._nextPCC;
    let inBranchDelay = read_bit_reg Cheri128_embed._inBranchDelay in
    if inBranchDelay then
       begin
         set_register Cheri128_embed._nextPC Cheri128_embed._delayedPC;
         set_register Cheri128_embed._nextPCC Cheri128_embed._delayedPCC;
       end
    else
       let pc_vaddr = unsigned_big(Cheri128_embed._PC) in
       let npc_addr = add_int_big_int 4 pc_vaddr in
       let npc_vec = to_vec_dec_big (bi64, npc_addr) in
       begin
         set_register Cheri128_embed._nextPC npc_vec;
         set_register Cheri128_embed._inCCallDelay (to_vec_dec_int (1, 0))
       end

  let get_pc () = unsigned_big (Cheri128_embed._PC)

  let translate_pc () = 
    try
      Some (unsigned_big(Cheri128_embed._TranslatePC(Cheri128_embed._PC)))
    with Sail_exit -> None

  let get_opcode pc_a = Cheri128_embed._reverse_endianness(_MEMr (to_vec_dec_big (bi64, pc_a), bi4))

  let decode = Cheri128_embed._decode

  let execute = Cheri128_embed._execute
  let is_halt i = (i = Cheri128_embed.HCF)
  let print_results () =
    begin
      resultf "DEBUG MIPS PC 0x%s\n" (big_int_to_hex (unsigned_big Cheri128_embed._PC));
      debug_print_gprs Cheri128_embed._GPR 0 31;
      resultf "DEBUG CAP PCC %s\n" (cap_reg_to_string Cheri128_embed._PCC);
      debug_print_caps Cheri128_embed._CapRegs 0 31;
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

let rec load_raw_file buf addr len chan =
    let to_read = min_int len page_size_bytes in
    really_input chan buf 0 to_read;
    add_mem_bytes addr buf 0 to_read;
    if (len > to_read) then
      load_raw_file buf (add_int_big_int to_read addr) (len - to_read) chan

let get_model = function
  | "cheri128" -> (module CHERI128_model : ISA_model)
  | "cheri" -> (module CHERI_model : ISA_model)
  | "mips" -> (module MIPS_model : ISA_model)
  | _ -> failwith "unknown model name"

let anon_raw s = 
  (* some input validation would be nice... *)
  let len = String.length s in
  let atidx = try
      String.index s '@' 
    with Not_found -> raise (Arg.Bad "expected argument of form file@addr") in
  let f = String.sub s 0 atidx in
  let addr =  String.sub s (atidx+1) (len - atidx -1) in
  raw_list := (!raw_list) @ [(f, big_int_of_string addr)]

let load_raw_arg (f, a) =
  let buf = Bytes.create page_size_bytes in
  let chan = open_in_bin f in
  let len = in_channel_length chan in
  load_raw_file buf a len chan

let run () =
  (* Turn off line-buffering of standard input to allow responsive console input  *)
  if Unix.isatty (Unix.stdin) then begin
    let tattrs = Unix.tcgetattr (Unix.stdin) in
    Unix.tcsetattr (Unix.stdin) (Unix.TCSANOW) ({tattrs with c_icanon=false})
  end;
  Arg.parse args anon_raw "" ;
  List.iter load_raw_arg !raw_list;
  let model = get_model !model_arg in
  let module Model = (val model  : ISA_model) in
  Model.init_model ();
  let (t, count) = time_it fde_loop (model, 0) in
  resultf "Execution time: %f seconds %f IPS \n" t (float(count) /. t);;

run () ;;
