(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Printf
open Format
open Big_int
open Interp_ast
open Interp_interface
open Interp_inter_imp
open Sail_impl_base
open Run_interp_model

open Sail_interface

module StringMap = Map.Make (String)

let file = ref ""

let rec foldli f acc ?(i = 0) = function [] -> acc | x :: xs -> foldli f (f i acc x) ~i:(i + 1) xs

let endian = ref E_big_endian

let hex_to_big_int s = big_int_of_int64 (Int64.of_string s)

let data_mem = (ref Mem.empty : memory_byte Run_interp_model.Mem.t ref)
let prog_mem = (ref Mem.empty : memory_byte Run_interp_model.Mem.t ref)
let tag_mem = (ref Mem.empty : memory_byte Run_interp_model.Mem.t ref)
let reg = ref Reg.empty
let input_buf = (ref [] : int list ref)

let add_mem byte addr mem =
  assert (byte >= 0 && byte < 256);
  (*Printf.printf "add_mem %s: 0x%02x\n" (Uint64.to_string_hex (Uint64.of_string (Nat_big_num.to_string addr))) byte;*)
  let mem_byte = memory_byte_of_int byte in
  let zero_byte = memory_byte_of_int 0 in
  mem := Mem.add addr mem_byte !mem;
  tag_mem := Mem.add addr zero_byte !tag_mem

let get_reg reg name =
  let reg_content = Reg.find name reg in
  reg_content

let rec load_memory_segment' (bytes, addr) mem =
  match bytes with
  | [] -> ()
  | byte :: bytes' ->
      let data_byte = Char.code byte in
      let addr' = Nat_big_num.succ addr in
      begin
        add_mem data_byte addr mem;
        load_memory_segment' (bytes', addr') mem
      end

let rec load_memory_segment (segment : Elf_interpreted_segment.elf64_interpreted_segment) mem =
  let (Byte_sequence.Sequence bytes) = segment.Elf_interpreted_segment.elf64_segment_body in
  let addr = segment.Elf_interpreted_segment.elf64_segment_paddr in
  load_memory_segment' (bytes, addr) mem

let rec load_memory_segments segments =
  begin
    match segments with
    | [] -> ()
    | segment :: segments' ->
        let x, w, r = segment.Elf_interpreted_segment.elf64_segment_flags in
        begin
          load_memory_segment segment prog_mem;
          load_memory_segments segments'
        end
  end

let rec read_mem mem address length =
  if length = 0 then []
  else (
    let byte = try Mem.find address mem with Not_found -> failwith "start address not found" in
    byte :: read_mem mem (Nat_big_num.succ address) (length - 1)
  )

let register_state_zero register_data rbn : register_value =
  let dir, width, start_index =
    try List.assoc rbn register_data with Not_found -> failwith ("register_state_zero lookup failed (" ^ rbn)
  in
  register_value_zeros dir width start_index

type model = PPC | AArch64 | MIPS
(*
let ppc_register_data_all =  [
  (*Pseudo registers*)
  ("CIA",   (D_increasing, 64, 0));
  ("NIA",   (D_increasing, 64, 0));
  ("mode64bit", (D_increasing, 1, 0));
  ("bigendianmode", (D_increasing, 1, 0));
  (* special registers *)
  ("CR",    (D_increasing, 32, 32));
  ("CTR",   (D_increasing, 64, 0 ));
  ("LR",    (D_increasing, 64, 0 ));
  ("XER",   (D_increasing, 64, 0 ));
  ("VRSAVE",(D_increasing, 32, 32));
  ("FPSCR", (D_increasing, 64, 0 ));
  ("VSCR",  (D_increasing, 32, 96));

  (* general purpose registers *)
  ("GPR0",  (D_increasing, 64, 0 ));
  ("GPR1",  (D_increasing, 64, 0 ));
  ("GPR2",  (D_increasing, 64, 0 ));
  ("GPR3",  (D_increasing, 64, 0 ));
  ("GPR4",  (D_increasing, 64, 0 ));
  ("GPR5",  (D_increasing, 64, 0 ));
  ("GPR6",  (D_increasing, 64, 0 ));
  ("GPR7",  (D_increasing, 64, 0 ));
  ("GPR8",  (D_increasing, 64, 0 ));
  ("GPR9",  (D_increasing, 64, 0 ));
  ("GPR10", (D_increasing, 64, 0 ));
  ("GPR11", (D_increasing, 64, 0 ));
  ("GPR12", (D_increasing, 64, 0 ));
  ("GPR13", (D_increasing, 64, 0 ));
  ("GPR14", (D_increasing, 64, 0 ));
  ("GPR15", (D_increasing, 64, 0 ));
  ("GPR16", (D_increasing, 64, 0 ));
  ("GPR17", (D_increasing, 64, 0 ));
  ("GPR18", (D_increasing, 64, 0 ));
  ("GPR19", (D_increasing, 64, 0 ));
  ("GPR20", (D_increasing, 64, 0 ));
  ("GPR21", (D_increasing, 64, 0 ));
  ("GPR22", (D_increasing, 64, 0 ));
  ("GPR23", (D_increasing, 64, 0 ));
  ("GPR24", (D_increasing, 64, 0 ));
  ("GPR25", (D_increasing, 64, 0 ));
  ("GPR26", (D_increasing, 64, 0 ));
  ("GPR27", (D_increasing, 64, 0 ));
  ("GPR28", (D_increasing, 64, 0 ));
  ("GPR29", (D_increasing, 64, 0 ));
  ("GPR30", (D_increasing, 64, 0 ));
  ("GPR31", (D_increasing, 64, 0 ));
  (* vector registers *)
  ("VR0",  (D_increasing, 128, 0 ));
  ("VR1",  (D_increasing, 128, 0 ));
  ("VR2",  (D_increasing, 128, 0 ));
  ("VR3",  (D_increasing, 128, 0 ));
  ("VR4",  (D_increasing, 128, 0 ));
  ("VR5",  (D_increasing, 128, 0 ));
  ("VR6",  (D_increasing, 128, 0 ));
  ("VR7",  (D_increasing, 128, 0 ));
  ("VR8",  (D_increasing, 128, 0 ));
  ("VR9",  (D_increasing, 128, 0 ));
  ("VR10", (D_increasing, 128, 0 ));
  ("VR11", (D_increasing, 128, 0 ));
  ("VR12", (D_increasing, 128, 0 ));
  ("VR13", (D_increasing, 128, 0 ));
  ("VR14", (D_increasing, 128, 0 ));
  ("VR15", (D_increasing, 128, 0 ));
  ("VR16", (D_increasing, 128, 0 ));
  ("VR17", (D_increasing, 128, 0 ));
  ("VR18", (D_increasing, 128, 0 ));
  ("VR19", (D_increasing, 128, 0 ));
  ("VR20", (D_increasing, 128, 0 ));
  ("VR21", (D_increasing, 128, 0 ));
  ("VR22", (D_increasing, 128, 0 ));
  ("VR23", (D_increasing, 128, 0 ));
  ("VR24", (D_increasing, 128, 0 ));
  ("VR25", (D_increasing, 128, 0 ));
  ("VR26", (D_increasing, 128, 0 ));
  ("VR27", (D_increasing, 128, 0 ));
  ("VR28", (D_increasing, 128, 0 ));
  ("VR29", (D_increasing, 128, 0 ));
  ("VR30", (D_increasing, 128, 0 ));
  ("VR31", (D_increasing, 128, 0 ));
  (* floating-point registers *)
  ("FPR0",  (D_increasing, 64, 0 ));
  ("FPR1",  (D_increasing, 64, 0 ));
  ("FPR2",  (D_increasing, 64, 0 ));
  ("FPR3",  (D_increasing, 64, 0 ));
  ("FPR4",  (D_increasing, 64, 0 ));
  ("FPR5",  (D_increasing, 64, 0 ));
  ("FPR6",  (D_increasing, 64, 0 ));
  ("FPR7",  (D_increasing, 64, 0 ));
  ("FPR8",  (D_increasing, 64, 0 ));
  ("FPR9",  (D_increasing, 64, 0 ));
  ("FPR10", (D_increasing, 64, 0 ));
  ("FPR11", (D_increasing, 64, 0 ));
  ("FPR12", (D_increasing, 64, 0 ));
  ("FPR13", (D_increasing, 64, 0 ));
  ("FPR14", (D_increasing, 64, 0 ));
  ("FPR15", (D_increasing, 64, 0 ));
  ("FPR16", (D_increasing, 64, 0 ));
  ("FPR17", (D_increasing, 64, 0 ));
  ("FPR18", (D_increasing, 64, 0 ));
  ("FPR19", (D_increasing, 64, 0 ));
  ("FPR20", (D_increasing, 64, 0 ));
  ("FPR21", (D_increasing, 64, 0 ));
  ("FPR22", (D_increasing, 64, 0 ));
  ("FPR23", (D_increasing, 64, 0 ));
  ("FPR24", (D_increasing, 64, 0 ));
  ("FPR25", (D_increasing, 64, 0 ));
  ("FPR26", (D_increasing, 64, 0 ));
  ("FPR27", (D_increasing, 64, 0 ));
  ("FPR28", (D_increasing, 64, 0 ));
  ("FPR29", (D_increasing, 64, 0 ));
  ("FPR30", (D_increasing, 64, 0 ));
  ("FPR31", (D_increasing, 64, 0 ));
]

let initial_stack_and_reg_data_of_PPC_elf_file e_entry all_data_memory =
  (* set up initial registers, per 3.4.1 of 64-bit PowerPC ELF Application Binary Interface Supplement 1.9 *)

  let auxiliary_vector_space = Nat_big_num.of_string "17592186042368" (*"0xffffffff800"*) in
  (* notionally there should be at least an AT_NULL auxiliary vector entry there, but our examples will never read it *)

  (* take start of stack roughly where running gdb on hello5 on bim says it is*)
  let initial_GPR1_stack_pointer = Nat_big_num.of_string "17592186040320" (*"0xffffffff000"*) in
  let initial_GPR1_stack_pointer_value =
    Sail_impl_base.register_value_of_integer 64 0 Sail_impl_base.D_increasing initial_GPR1_stack_pointer in
  (* ELF says we need an initial zero doubleword there *)
  let initial_stack_data =
    (* the code actually uses the stack, both above and below, so we map a bit more memory*)
    (* this is a fairly big but arbitrary chunk *)
    (* let initial_stack_data_address = Nat_big_num.sub initial_GPR1_stack_pointer (Nat_big_num.of_int 128) in
        [("initial_stack_data", initial_stack_data_address, Lem_list.replicate (128+32) 0 ))] in *)
    (* this is the stack memory that test 1938 actually uses *)
    [ ("initial_stack_data1", Nat_big_num.sub initial_GPR1_stack_pointer (Nat_big_num.of_int 128),
       Lem_list.replicate 8 0 );
      ("initial_stack_data2", Nat_big_num.sub initial_GPR1_stack_pointer (Nat_big_num.of_int 8),
       Lem_list.replicate 8  0 );
      ("initial_stack_data3", Nat_big_num.add initial_GPR1_stack_pointer (Nat_big_num.of_int 16),
       Lem_list.replicate 8  0 )] in
  
  (* read TOC from the second field of the function descriptor pointed to by e_entry*)
  let initial_GPR2_TOC =
    Sail_impl_base.register_value_of_address
      (Sail_impl_base.address_of_byte_list
         (List.map (fun b -> match b with Some b -> b | None -> failwith "Address had undefined")
             (List.map byte_of_byte_lifted
                (read_mem all_data_memory
                   (Nat_big_num.add (Nat_big_num.of_int 8) e_entry) 8))))
      Sail_impl_base.D_increasing in
  (* these initial register values are all mandated to be zero, but that's handled by the generic zeroing below
      let initial_GPR3_argc = (Nat_big_num.of_int 0) in
      let initial_GPR4_argv = (Nat_big_num.of_int 0) in
      let initial_GPR5_envp = (Nat_big_num.of_int 0) in
      let initial_FPSCR = (Nat_big_num.of_int 0) in
  *)
  let initial_register_abi_data : (string * Sail_impl_base.register_value) list =
    [ ("GPR1", initial_GPR1_stack_pointer_value);
      ("GPR2", initial_GPR2_TOC);
  (*
    ("GPR3", initial_GPR3_argc);
    ("GPR4", initial_GPR4_argv);
    ("GPR5", initial_GPR5_envp);
    ("FPSCR", initial_FPSCR);
    *)
    ] in

  (initial_stack_data, initial_register_abi_data)


let aarch64_reg bit_count name = (name, (D_decreasing, bit_count, bit_count - 1))

let aarch64_PC_data = [aarch64_reg 64 "_PC"]

(* most of the PSTATE fields are aliases to other registers so they
   don't appear here *)
let aarch64_PSTATE_data  = [
  aarch64_reg 1 "PSTATE_nRW";
  aarch64_reg 1 "PSTATE_E";
  aarch64_reg 5 "PSTATE_M";
]

let aarch64_general_purpose_registers_data = [
  aarch64_reg 64 "R0";
  aarch64_reg 64 "R1";
  aarch64_reg 64 "R2";
  aarch64_reg 64 "R3";
  aarch64_reg 64 "R4";
  aarch64_reg 64 "R5";
  aarch64_reg 64 "R6";
  aarch64_reg 64 "R7";
  aarch64_reg 64 "R8";
  aarch64_reg 64 "R9";
  aarch64_reg 64 "R10";
  aarch64_reg 64 "R11";
  aarch64_reg 64 "R12";
  aarch64_reg 64 "R13";
  aarch64_reg 64 "R14";
  aarch64_reg 64 "R15";
  aarch64_reg 64 "R16";
  aarch64_reg 64 "R17";
  aarch64_reg 64 "R18";
  aarch64_reg 64 "R19";
  aarch64_reg 64 "R20";
  aarch64_reg 64 "R21";
  aarch64_reg 64 "R22";
  aarch64_reg 64 "R23";
  aarch64_reg 64 "R24";
  aarch64_reg 64 "R25";
  aarch64_reg 64 "R26";
  aarch64_reg 64 "R27";
  aarch64_reg 64 "R28";
  aarch64_reg 64 "R29";
  aarch64_reg 64 "R30";
]

let aarch64_SIMD_registers_data = [
  aarch64_reg 128 "V0";
  aarch64_reg 128 "V1";
  aarch64_reg 128 "V2";
  aarch64_reg 128 "V3";
  aarch64_reg 128 "V4";
  aarch64_reg 128 "V5";
  aarch64_reg 128 "V6";
  aarch64_reg 128 "V7";
  aarch64_reg 128 "V8";
  aarch64_reg 128 "V9";
  aarch64_reg 128 "V10";
  aarch64_reg 128 "V11";
  aarch64_reg 128 "V12";
  aarch64_reg 128 "V13";
  aarch64_reg 128 "V14";
  aarch64_reg 128 "V15";
  aarch64_reg 128 "V16";
  aarch64_reg 128 "V17";
  aarch64_reg 128 "V18";
  aarch64_reg 128 "V19";
  aarch64_reg 128 "V20";
  aarch64_reg 128 "V21";
  aarch64_reg 128 "V22";
  aarch64_reg 128 "V23";
  aarch64_reg 128 "V24";
  aarch64_reg 128 "V25";
  aarch64_reg 128 "V26";
  aarch64_reg 128 "V27";
  aarch64_reg 128 "V28";
  aarch64_reg 128 "V29";
  aarch64_reg 128 "V30";
  aarch64_reg 128 "V31";
]

let aarch64_special_purpose_registers_data = [
  aarch64_reg 32 "CurrentEL";
  aarch64_reg 32 "DAIF";
  aarch64_reg 32 "NZCV";
  aarch64_reg 64 "SP_EL0";
  aarch64_reg 64 "SP_EL1";
  aarch64_reg 64 "SP_EL2";
  aarch64_reg 64 "SP_EL3";
  aarch64_reg 32 "SPSel";
  aarch64_reg 32 "SPSR_EL1";
  aarch64_reg 32 "SPSR_EL2";
  aarch64_reg 32 "SPSR_EL3";
  aarch64_reg 64 "ELR_EL1";
  aarch64_reg 64 "ELR_EL2";
  aarch64_reg 64 "ELR_EL3";
]

let aarch64_general_system_control_registers_data = [
  aarch64_reg 64 "HCR_EL2";
  aarch64_reg 64 "ID_AA64MMFR0_EL1";
  aarch64_reg 64 "RVBAR_EL1";
  aarch64_reg 64 "RVBAR_EL2";
  aarch64_reg 64 "RVBAR_EL3";
  aarch64_reg 32 "SCR_EL3";
  aarch64_reg 32 "SCTLR_EL1";
  aarch64_reg 32 "SCTLR_EL2";
  aarch64_reg 32 "SCTLR_EL3";
  aarch64_reg 64 "TCR_EL1";
  aarch64_reg 32 "TCR_EL2";
  aarch64_reg 32 "TCR_EL3";
]

let aarch64_debug_registers_data = [
  aarch64_reg 32 "DBGPRCR_EL1";
  aarch64_reg 32 "OSDLR_EL1";
]

let aarch64_performance_monitors_registers_data = []
let aarch64_generic_timer_registers_data = []
let aarch64_generic_interrupt_controller_CPU_interface_registers_data = []

let aarch64_external_debug_registers_data = [
  aarch64_reg 32 "EDSCR";
]

let aarch32_general_system_control_registers_data = [
  aarch64_reg 32 "SCR";
]

let aarch32_debug_registers_data = [
  aarch64_reg 32 "DBGOSDLR";
  aarch64_reg 32 "DBGPRCR";
]

let aarch64_register_data_all =
  aarch64_PC_data @
  aarch64_PSTATE_data @
  aarch64_general_purpose_registers_data @
  aarch64_SIMD_registers_data @
  aarch64_special_purpose_registers_data @
  aarch64_general_system_control_registers_data @
  aarch64_debug_registers_data @
  aarch64_performance_monitors_registers_data @
  aarch64_generic_timer_registers_data @
  aarch64_generic_interrupt_controller_CPU_interface_registers_data @
  aarch64_external_debug_registers_data @
  aarch32_general_system_control_registers_data @
  aarch32_debug_registers_data

let initial_stack_and_reg_data_of_AAarch64_elf_file e_entry all_data_memory =
  let (reg_SP_EL0_direction, reg_SP_EL0_width, reg_SP_EL0_initial_index) =
    List.assoc "SP_EL0" aarch64_register_data_all in
  
  (* we compiled a small program that prints out SP and run it a few
      times on the Nexus9, these are the results:
      0x0000007fe7f903e0
      0x0000007fdcdbf3f0
      0x0000007fcbe1ba90
      0x0000007fcf378280
      0x0000007fdd54b8d0
      0x0000007fd961bc10
      0x0000007ff3be6350
      0x0000007fd6bf6ef0
      0x0000007fff7676f0
      0x0000007ff2c34560 *)
  let initial_SP_EL0 = Nat_big_num.of_string "549739036672" (*"0x0000007fff000000"*) in
  let initial_SP_EL0_value =
    Sail_impl_base.register_value_of_integer
      reg_SP_EL0_width
      reg_SP_EL0_initial_index
      reg_SP_EL0_direction
      initial_SP_EL0
  in

  (* ELF says we need an initial zero doubleword there *)
  (* the code actually uses the stack, both above and below, so we map a bit more memory*)
  let initial_stack_data =
    (* this is a fairly big but arbitrary chunk: *)
    (* let initial_stack_data_address = Nat_big_num.sub initial_GPR1_stack_pointer (Nat_big_num.of_int 128) in
        [("initial_stack_data", initial_stack_data_address, Lem_list.replicate (128+32) 0 ))] in *)
    
    [ ("initial_stack_data1", Nat_big_num.sub initial_SP_EL0 (Nat_big_num.of_int 16),  Lem_list.replicate 8 0);
      ("initial_stack_data2", Nat_big_num.sub initial_SP_EL0 (Nat_big_num.of_int 8),   Lem_list.replicate 8 0)
    ]
  in

  let initial_register_abi_data : (string * Sail_impl_base.register_value) list =
    [("SP_EL0", initial_SP_EL0_value)]
  in

  (initial_stack_data, initial_register_abi_data)
*)

let mips_register_data_all =
  [
    (*Pseudo registers*)
    ("PC", (D_decreasing, 64, 63));
    ("branchPending", (D_decreasing, 1, 0));
    ("inBranchDelay", (D_decreasing, 1, 0));
    ("delayedPC", (D_decreasing, 64, 63));
    ("nextPC", (D_decreasing, 64, 63));
    (* General purpose registers *)
    ("GPR00", (D_decreasing, 64, 63));
    ("GPR01", (D_decreasing, 64, 63));
    ("GPR02", (D_decreasing, 64, 63));
    ("GPR03", (D_decreasing, 64, 63));
    ("GPR04", (D_decreasing, 64, 63));
    ("GPR05", (D_decreasing, 64, 63));
    ("GPR06", (D_decreasing, 64, 63));
    ("GPR07", (D_decreasing, 64, 63));
    ("GPR08", (D_decreasing, 64, 63));
    ("GPR09", (D_decreasing, 64, 63));
    ("GPR10", (D_decreasing, 64, 63));
    ("GPR11", (D_decreasing, 64, 63));
    ("GPR12", (D_decreasing, 64, 63));
    ("GPR13", (D_decreasing, 64, 63));
    ("GPR14", (D_decreasing, 64, 63));
    ("GPR15", (D_decreasing, 64, 63));
    ("GPR16", (D_decreasing, 64, 63));
    ("GPR17", (D_decreasing, 64, 63));
    ("GPR18", (D_decreasing, 64, 63));
    ("GPR19", (D_decreasing, 64, 63));
    ("GPR20", (D_decreasing, 64, 63));
    ("GPR21", (D_decreasing, 64, 63));
    ("GPR22", (D_decreasing, 64, 63));
    ("GPR23", (D_decreasing, 64, 63));
    ("GPR24", (D_decreasing, 64, 63));
    ("GPR25", (D_decreasing, 64, 63));
    ("GPR26", (D_decreasing, 64, 63));
    ("GPR27", (D_decreasing, 64, 63));
    ("GPR28", (D_decreasing, 64, 63));
    ("GPR29", (D_decreasing, 64, 63));
    ("GPR30", (D_decreasing, 64, 63));
    ("GPR31", (D_decreasing, 64, 63));
    (* special registers for mul/div *)
    ("HI", (D_decreasing, 64, 63));
    ("LO", (D_decreasing, 64, 63));
    (* control registers *)
    ("CP0Status", (D_decreasing, 32, 31));
    ("CP0Cause", (D_decreasing, 32, 31));
    ("CP0EPC", (D_decreasing, 64, 63));
    ("CP0LLAddr", (D_decreasing, 64, 63));
    ("CP0LLBit", (D_decreasing, 1, 0));
    ("CP0Count", (D_decreasing, 32, 31));
    ("CP0Compare", (D_decreasing, 32, 31));
    ("CP0HWREna", (D_decreasing, 32, 31));
    ("CP0UserLocal", (D_decreasing, 64, 63));
    ("CP0BadVAddr", (D_decreasing, 64, 63));
    ("TLBProbe", (D_decreasing, 1, 0));
    ("TLBIndex", (D_decreasing, 6, 5));
    ("TLBRandom", (D_decreasing, 6, 5));
    ("TLBEntryLo0", (D_decreasing, 64, 63));
    ("TLBEntryLo1", (D_decreasing, 64, 63));
    ("TLBContext", (D_decreasing, 64, 63));
    ("TLBPageMask", (D_decreasing, 16, 15));
    ("TLBWired", (D_decreasing, 6, 5));
    ("TLBEntryHi", (D_decreasing, 64, 63));
    ("TLBXContext", (D_decreasing, 64, 63));
    ("TLBEntry00", (D_decreasing, 117, 116));
    ("TLBEntry01", (D_decreasing, 117, 116));
    ("TLBEntry02", (D_decreasing, 117, 116));
    ("TLBEntry03", (D_decreasing, 117, 116));
    ("TLBEntry04", (D_decreasing, 117, 116));
    ("TLBEntry05", (D_decreasing, 117, 116));
    ("TLBEntry06", (D_decreasing, 117, 116));
    ("TLBEntry07", (D_decreasing, 117, 116));
    ("TLBEntry08", (D_decreasing, 117, 116));
    ("TLBEntry09", (D_decreasing, 117, 116));
    ("TLBEntry10", (D_decreasing, 117, 116));
    ("TLBEntry11", (D_decreasing, 117, 116));
    ("TLBEntry12", (D_decreasing, 117, 116));
    ("TLBEntry13", (D_decreasing, 117, 116));
    ("TLBEntry14", (D_decreasing, 117, 116));
    ("TLBEntry15", (D_decreasing, 117, 116));
    ("TLBEntry16", (D_decreasing, 117, 116));
    ("TLBEntry17", (D_decreasing, 117, 116));
    ("TLBEntry18", (D_decreasing, 117, 116));
    ("TLBEntry19", (D_decreasing, 117, 116));
    ("TLBEntry20", (D_decreasing, 117, 116));
    ("TLBEntry21", (D_decreasing, 117, 116));
    ("TLBEntry22", (D_decreasing, 117, 116));
    ("TLBEntry23", (D_decreasing, 117, 116));
    ("TLBEntry24", (D_decreasing, 117, 116));
    ("TLBEntry25", (D_decreasing, 117, 116));
    ("TLBEntry26", (D_decreasing, 117, 116));
    ("TLBEntry27", (D_decreasing, 117, 116));
    ("TLBEntry28", (D_decreasing, 117, 116));
    ("TLBEntry29", (D_decreasing, 117, 116));
    ("TLBEntry30", (D_decreasing, 117, 116));
    ("TLBEntry31", (D_decreasing, 117, 116));
    ("TLBEntry32", (D_decreasing, 117, 116));
    ("TLBEntry33", (D_decreasing, 117, 116));
    ("TLBEntry34", (D_decreasing, 117, 116));
    ("TLBEntry35", (D_decreasing, 117, 116));
    ("TLBEntry36", (D_decreasing, 117, 116));
    ("TLBEntry37", (D_decreasing, 117, 116));
    ("TLBEntry38", (D_decreasing, 117, 116));
    ("TLBEntry39", (D_decreasing, 117, 116));
    ("TLBEntry40", (D_decreasing, 117, 116));
    ("TLBEntry41", (D_decreasing, 117, 116));
    ("TLBEntry42", (D_decreasing, 117, 116));
    ("TLBEntry43", (D_decreasing, 117, 116));
    ("TLBEntry44", (D_decreasing, 117, 116));
    ("TLBEntry45", (D_decreasing, 117, 116));
    ("TLBEntry46", (D_decreasing, 117, 116));
    ("TLBEntry47", (D_decreasing, 117, 116));
    ("TLBEntry48", (D_decreasing, 117, 116));
    ("TLBEntry49", (D_decreasing, 117, 116));
    ("TLBEntry50", (D_decreasing, 117, 116));
    ("TLBEntry51", (D_decreasing, 117, 116));
    ("TLBEntry52", (D_decreasing, 117, 116));
    ("TLBEntry53", (D_decreasing, 117, 116));
    ("TLBEntry54", (D_decreasing, 117, 116));
    ("TLBEntry55", (D_decreasing, 117, 116));
    ("TLBEntry56", (D_decreasing, 117, 116));
    ("TLBEntry57", (D_decreasing, 117, 116));
    ("TLBEntry58", (D_decreasing, 117, 116));
    ("TLBEntry59", (D_decreasing, 117, 116));
    ("TLBEntry60", (D_decreasing, 117, 116));
    ("TLBEntry61", (D_decreasing, 117, 116));
    ("TLBEntry62", (D_decreasing, 117, 116));
    ("TLBEntry63", (D_decreasing, 117, 116));
    ("UART_WDATA", (D_decreasing, 8, 7));
    ("UART_RDATA", (D_decreasing, 8, 7));
    ("UART_WRITTEN", (D_decreasing, 1, 0));
    ("UART_RVALID", (D_decreasing, 1, 0));
  ]

let initial_stack_and_reg_data_of_MIPS_elf_file e_entry all_data_memory =
  let initial_stack_data = [] in
  let initial_register_abi_data : (string * Sail_impl_base.register_value) list =
    [("CP0Status", Sail_impl_base.register_value_of_integer 32 31 D_decreasing (Nat_big_num.of_string "0x00400000"))]
  in
  (initial_stack_data, initial_register_abi_data)

let initial_reg_file reg_data init =
  List.iter (fun (reg_name, _) -> reg := Reg.add reg_name (init reg_name) !reg) reg_data

let initial_system_state_of_elf_file name =
  (* call ELF analyser on file *)
  match Sail_interface.populate_and_obtain_global_symbol_init_info name with
  | Error.Fail s -> failwith ("populate_and_obtain_global_symbol_init_info: " ^ s)
  | Error.Success
      (_, (elf_epi : Sail_interface.executable_process_image), (symbol_map : Elf_file.global_symbol_init_info)) ->
      let segments, e_entry, e_machine =
        begin
          match elf_epi with
          | ELF_Class_32 _ -> failwith "cannot handle ELF_Class_32"
          | ELF_Class_64 (segments, e_entry, e_machine) ->
              (* remove all the auto generated segments (they contain only 0s) *)
              let segments =
                Lem_list.mapMaybe (fun (seg, prov) -> if prov = Elf_file.FromELF then Some seg else None) segments
              in
              (segments, e_entry, e_machine)
        end
      in

      (* construct program memory and start address *)
      begin
        prog_mem := Mem.empty;
        data_mem := Mem.empty;
        tag_mem := Mem.empty;
        load_memory_segments segments;
        (*
      debugf "prog_mem\n";
      Mem.iter (fun k v -> debugf "%s\n" (Mem.to_string k v)) !prog_mem;
      debugf "data_mem\n";
      Mem.iter (fun k v -> debugf "%s\n" (Mem.to_string k v)) !data_mem;
      *)
        let ( isa_defs,
              isa_memory_access,
              isa_externs,
              isa_model,
              model_reg_d,
              startaddr,
              initial_stack_data,
              initial_register_abi_data,
              register_data_all ) =
          match Nat_big_num.to_int e_machine with
          (* | 21  (* EM_PPC64 *) ->
                  let startaddr =
                    let e_entry = Uint64.of_int64 (Nat_big_num.to_int64 e_entry) in
                    match Abi_power64.abi_power64_compute_program_entry_point segments e_entry with
                    | Error.Fail s -> failwith "Failed computing entry point"
                    | Error.Success s -> Nat_big_num.of_int64 (Uint64.to_int64 s)
                  in
                  let (initial_stack_data, initial_register_abi_data) =
                    initial_stack_and_reg_data_of_PPC_elf_file e_entry !data_mem in

                    (Power.defs,
                     (Power_extras.read_memory_functions,Power_extras.memory_writes,[],[],Power_extras.barrier_functions),
                     Power_extras.power_externs,
                     PPC,
                     D_increasing,
                     startaddr,
                     initial_stack_data,
                     initial_register_abi_data,
                     ppc_register_data_all)

                | 183 (* EM_AARCH64 *) ->
                  let startaddr =
                    let e_entry = Uint64.of_int64 (Nat_big_num.to_int64 e_entry) in
                    match Abi_aarch64_le.abi_aarch64_le_compute_program_entry_point segments e_entry with
                    | Error.Fail s -> failwith "Failed computing entry point"
                    | Error.Success s -> Nat_big_num.of_int64 (Uint64.to_int64 s)
                  in

                  let (initial_stack_data, initial_register_abi_data) =
                    initial_stack_and_reg_data_of_AAarch64_elf_file e_entry !data_mem in

                  (ArmV8.defs,
                   (ArmV8_extras.aArch64_read_memory_functions,
                    ArmV8_extras.aArch64_memory_writes,
             ArmV8_extras.aArch64_memory_eas,
             ArmV8_extras.aArch64_memory_vals,
                    ArmV8_extras.aArch64_barrier_functions),
                   [],
                   AArch64,
                   D_decreasing,
                   startaddr,
                   initial_stack_data,
                   initial_register_abi_data,
                   aarch64_register_data_all) *)
          | 8 (* EM_MIPS *) ->
              let startaddr =
                let e_entry = Uint64_wrapper.of_bigint e_entry in
                match Abi_mips64.abi_mips64_compute_program_entry_point segments e_entry with
                | Error.Fail s -> failwith "Failed computing entry point"
                | Error.Success s -> s
              in
              let initial_stack_data, initial_register_abi_data =
                initial_stack_and_reg_data_of_MIPS_elf_file e_entry !data_mem
              in

              ( Mips.defs,
                ( Mips_extras.mips_read_memory_functions,
                  Mips_extras.mips_memory_writes,
                  Mips_extras.mips_memory_eas,
                  Mips_extras.mips_memory_vals,
                  Mips_extras.mips_barrier_functions
                ),
                [],
                MIPS,
                D_decreasing,
                startaddr,
                initial_stack_data,
                initial_register_abi_data,
                mips_register_data_all
              )
          | _ ->
              failwith
                (Printf.sprintf
                   "Sail sequential interpreter can't handle the e_machine value %s, only EM_PPC64, EM_AARCH64 and \
                    EM_MIPS are supported."
                   (Nat_big_num.to_string e_machine)
                )
        in

        (* pull the object symbols from the symbol table *)
        let symbol_table : (string * Nat_big_num.num * int * word8 list (*their bytes*)) list =
          let rec convert_symbol_table symbol_map =
            begin
              match symbol_map with
              | [] -> []
              | ( (name : string),
                  ( (typ : Nat_big_num.num),
                    (size : Nat_big_num.num (*number of bytes*)),
                    (address : Nat_big_num.num),
                    (mb : Byte_sequence.byte_sequence option (*present iff type=stt_object*)),
                    (binding : Nat_big_num.num)
                  )
                ) (*              (mb: Byte_sequence_wrapper.t option (*present iff type=stt_object*)) )) *)
                :: symbol_map' ->
                  if
                    Nat_big_num.equal typ Elf_symbol_table.stt_object
                    && not (Nat_big_num.equal size (Nat_big_num.of_int 0))
                  then (
                    (* an object symbol - map *)
                    (*Printf.printf "*** size %d ***\n" (Nat_big_num.to_int size);*)
                    let bytes =
                      match mb with
                      | None -> raise (Failure "this cannot happen")
                      | Some (Sequence bytes) -> List.map (fun (c : char) -> Char.code c) bytes
                    in
                    (name, address, List.length bytes, bytes) :: convert_symbol_table symbol_map'
                  )
                  else (* not an object symbol or of zero size - ignore *)
                    convert_symbol_table symbol_map'
            end
          in
          List.map (fun (n, a, bs) -> (n, a, List.length bs, bs)) initial_stack_data @ convert_symbol_table symbol_map
        in

        (* invert the symbol table to use for pp *)
        let symbol_table_pp : ((Sail_impl_base.address * int) * string) list =
          (* map symbol to (bindings, footprint),
             if a symbol appears more then onece keep the one with higher
             precedence (stb_global > stb_weak > stb_local) *)
          let map =
            List.fold_left
              (fun map (name, (typ, size, address, mb, binding)) ->
                if
                  String.length name <> 0
                  && (if String.length name = 1 then Char.code (String.get name 0) <> 0 else true)
                  && not (Nat_big_num.equal address (Nat_big_num.of_int 0))
                then (
                  try
                    let binding', _ = StringMap.find name map in
                    if
                      Nat_big_num.equal binding' Elf_symbol_table.stb_local
                      || Nat_big_num.equal binding Elf_symbol_table.stb_global
                    then
                      StringMap.add name
                        (binding, (Sail_impl_base.address_of_integer address, Nat_big_num.to_int size))
                        map
                    else map
                  with Not_found ->
                    StringMap.add name
                      (binding, (Sail_impl_base.address_of_integer address, Nat_big_num.to_int size))
                      map
                )
                else map
              )
              StringMap.empty symbol_map
          in

          List.map (fun (name, (binding, fp)) -> (fp, name)) (StringMap.bindings map)
        in

        (* Now we examine the rest of the data memory,
           removing the footprint of the symbols and chunking it into aligned chunks *)
        let rec remove_symbols_from_data_memory data_mem symbols =
          match symbols with
          | [] -> data_mem
          | (name, address, size, bs) :: symbols' ->
              let data_mem' =
                Mem.filter
                  (fun a v ->
                    not
                      (Nat_big_num.greater_equal a address
                      && Nat_big_num.less a (Nat_big_num.add (Nat_big_num.of_int (List.length bs)) address)
                      )
                  )
                  data_mem
              in
              remove_symbols_from_data_memory data_mem' symbols'
        in

        let trimmed_data_memory : (Nat_big_num.num * memory_byte) list =
          Mem.bindings (remove_symbols_from_data_memory !data_mem symbol_table)
        in

        (* make sure that's ordered increasingly.... *)
        let trimmed_data_memory = List.sort (fun (a, b) (a', b') -> Nat_big_num.compare a a') trimmed_data_memory in

        let aligned a n =
          (* a mod n = 0 *)
          let n_big = Nat_big_num.of_int n in
          Nat_big_num.equal (Nat_big_num.modulus a n_big) (Nat_big_num.of_int 0)
        in

        let isplus a' a n =
          (* a' = a+n *)
          Nat_big_num.equal a' (Nat_big_num.add (Nat_big_num.of_int n) a)
        in

        let rec chunk_data_memory dm =
          match dm with
          | (a0, b0) :: (a1, b1) :: (a2, b2) :: (a3, b3) :: (a4, b4) :: (a5, b5) :: (a6, b6) :: (a7, b7) :: dm'
            when aligned a0 8 && isplus a1 a0 1 && isplus a2 a0 2 && isplus a3 a0 3 && isplus a4 a0 4 && isplus a5 a0 5
                 && isplus a6 a0 6 && isplus a7 a0 7 ->
              (a0, 8, [b0; b1; b2; b3; b4; b5; b6; b7]) :: chunk_data_memory dm'
          | (a0, b0) :: (a1, b1) :: (a2, b2) :: (a3, b3) :: dm'
            when aligned a0 4 && isplus a1 a0 1 && isplus a2 a0 2 && isplus a3 a0 3 ->
              (a0, 4, [b0; b1; b2; b3]) :: chunk_data_memory dm'
          | (a0, b0) :: (a1, b1) :: dm' when aligned a0 2 && isplus a1 a0 1 ->
              (a0, 2, [b0; b1]) :: chunk_data_memory dm'
          | (a0, b0) :: dm' -> (a0, 1, [b0]) :: chunk_data_memory dm'
          | [] -> []
        in

        let initial_register_state rbn =
          try List.assoc rbn initial_register_abi_data with Not_found -> (register_state_zero register_data_all) rbn
        in

        begin
          initial_reg_file register_data_all initial_register_state;

          (* construct initial system state *)
          let initial_system_state =
            ( isa_defs,
              isa_memory_access,
              isa_externs,
              isa_model,
              model_reg_d,
              startaddr,
              Sail_impl_base.address_of_integer startaddr
            )
          in

          (initial_system_state, symbol_table_pp)
        end
      end

let eager_eval = ref true
let break_point = ref false
let break_instr = ref 0
let max_cut_off = ref false
let max_instr = ref 0
let raw_file = ref ""
let raw_at = ref 0

let args =
  [
    ("--file", Arg.Set_string file, "filename of elf binary to load in memory");
    ("--quiet", Arg.Clear Run_interp_model.interact_print, "do not display per-instruction actions");
    ( "--silent",
      Arg.Tuple
        [
          Arg.Clear Run_interp_model.error_print;
          Arg.Clear Run_interp_model.interact_print;
          Arg.Clear Run_interp_model.result_print;
        ],
      "do not dispaly error messages, per-instruction actions, or results"
    );
    ("--no_result", Arg.Clear Run_interp_model.result_print, "do not display final register values");
    ("--interactive", Arg.Clear eager_eval, "interactive execution");
    ( "--breakpoint",
      Arg.Int
        (fun i ->
          break_point := true;
          break_instr := i
        ),
      "run to instruction number i, then run interactively"
    );
    ( "--max_instruction",
      Arg.Int
        (fun i ->
          max_cut_off := true;
          max_instr := i
        ),
      "only run i instructions, then stop"
    );
    ("--raw", Arg.Set_string raw_file, "filename of raw file to load in memory");
    ("--at", Arg.Set_int raw_at, "address to load raw file in memory");
  ]

let time_it action arg =
  let start_time = Sys.time () in
  ignore (action arg);
  let finish_time = Sys.time () in
  finish_time -. start_time

(*TODO MIPS specific, should print final register values under all models*)
let rec debug_print_gprs start stop =
  resultf "DEBUG MIPS REG %.2d %s\n" start
    (Printing_functions.logfile_register_value_to_string (Reg.find (Format.sprintf "GPR%02d" start) !reg));
  if start < stop then debug_print_gprs (start + 1) stop else ()

let stop_condition_met model instr =
  match model with
  | PPC -> (
      match instr with
      | "Sc", [("Lev", _, arg)] -> Nat_big_num.equal (integer_of_bit_list arg) (Nat_big_num.of_int 32)
      | _ -> false
    )
  | AArch64 -> (
      match instr with "ImplementationDefinedStopFetching", _ -> true | _ -> false
    )
  | MIPS -> (
      match instr with
      | "HCF", _ ->
          resultf "DEBUG MIPS PC %s\n" (Printing_functions.logfile_register_value_to_string (Reg.find "PC" !reg));
          debug_print_gprs 0 31;
          true
      | _ -> false
    )

let is_branch model instruction =
  let name, _, _ = instruction in
  match (model, name) with
  | PPC, "B" -> true
  | PPC, "Bc" -> true
  | PPC, "Bclr" -> true
  | PPC, "Bcctr" -> true
  | PPC, _ -> false
  | AArch64, "BranchImmediate" -> true
  | AArch64, "BranchConditional" -> true
  | AArch64, "CompareAndBranch" -> true
  | AArch64, "TestBitAndBranch" -> true
  | AArch64, "BranchRegister" -> true
  | AArch64, _ -> false
  | MIPS, _ -> false (*todo,fill this in*)

let option_int_of_option_integer i = match i with Some i -> Some (Nat_big_num.to_int i) | None -> None

let set_next_instruction_address model =
  match model with
  | PPC -> (
      let cia = Reg.find "CIA" !reg in
      let cia_addr = address_of_register_value cia in
      match cia_addr with
      | Some cia_addr ->
          let nia_addr = add_address_nat cia_addr 4 in
          let nia = register_value_of_address nia_addr Sail_impl_base.D_increasing in
          reg := Reg.add "NIA" nia !reg
      | _ -> failwith "CIA address contains unknown or undefined"
    )
  | AArch64 -> (
      let pc = Reg.find "_PC" !reg in
      let pc_addr = address_of_register_value pc in
      match pc_addr with
      | Some pc_addr ->
          let n_addr = add_address_nat pc_addr 4 in
          let n_pc = register_value_of_address n_addr D_decreasing in
          reg := Reg.add "_PC" n_pc !reg
      | _ -> failwith "_PC address contains unknown or undefined"
    )
  | MIPS -> (
      let pc_addr = address_of_register_value (Reg.find "PC" !reg) in
      let branchPending = integer_of_register_value (Reg.find "branchPending" !reg) in
      match (pc_addr, option_int_of_option_integer branchPending) with
      | Some pc_val, Some 0 ->
          (* normal -- increment PC *)
          let n_addr = add_address_nat pc_val 4 in
          let n_pc = register_value_of_address n_addr D_decreasing in
          begin
            reg := Reg.add "nextPC" n_pc !reg;
            reg :=
              Reg.add "inBranchDelay" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero) !reg
          end
      | Some pc_val, Some 1 -> begin
          (* delay slot -- branch to delayed PC and clear branchPending *)
          reg := Reg.add "nextPC" (Reg.find "delayedPC" !reg) !reg;
          reg :=
            Reg.add "branchPending" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero) !reg;
          reg :=
            Reg.add "inBranchDelay"
              (register_value_of_integer 1 0 Sail_impl_base.D_decreasing (Nat_big_num.of_int 1))
              !reg
        end
      | _, _ ->
          errorf "PC address contains unknown or undefined";
          exit 1
    )

let add1 = Nat_big_num.add (Nat_big_num.of_int 1)

let get_addr_trans_regs _ =
  Some
    [
      (Sail_impl_base.Reg ("PC", 63, 64, Sail_impl_base.D_decreasing), Reg.find "PC" !reg);
      (Sail_impl_base.Reg ("CP0Status", 31, 32, Sail_impl_base.D_decreasing), Reg.find "CP0Status" !reg);
      (Sail_impl_base.Reg ("CP0Cause", 31, 32, Sail_impl_base.D_decreasing), Reg.find "CP0Cause" !reg);
      (Sail_impl_base.Reg ("CP0Count", 31, 32, Sail_impl_base.D_decreasing), Reg.find "CP0Count" !reg);
      (Sail_impl_base.Reg ("CP0Compare", 31, 32, Sail_impl_base.D_decreasing), Reg.find "CP0Compare" !reg);
      (Sail_impl_base.Reg ("inBranchDelay", 0, 1, Sail_impl_base.D_decreasing), Reg.find "inBranchDelay" !reg);
      (Sail_impl_base.Reg ("TLBRandom", 5, 6, Sail_impl_base.D_decreasing), Reg.find "TLBRandom" !reg);
      (Sail_impl_base.Reg ("TLBWired", 5, 6, Sail_impl_base.D_decreasing), Reg.find "TLBWired" !reg);
      (Sail_impl_base.Reg ("TLBEntryHi", 63, 64, Sail_impl_base.D_decreasing), Reg.find "TLBEntryHi" !reg);
      (Sail_impl_base.Reg ("TLBEntry00", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry00" !reg);
      (Sail_impl_base.Reg ("TLBEntry01", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry01" !reg);
      (Sail_impl_base.Reg ("TLBEntry02", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry02" !reg);
      (Sail_impl_base.Reg ("TLBEntry03", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry03" !reg);
      (Sail_impl_base.Reg ("TLBEntry04", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry04" !reg);
      (Sail_impl_base.Reg ("TLBEntry05", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry05" !reg);
      (Sail_impl_base.Reg ("TLBEntry06", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry06" !reg);
      (Sail_impl_base.Reg ("TLBEntry07", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry07" !reg);
      (Sail_impl_base.Reg ("TLBEntry08", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry08" !reg);
      (Sail_impl_base.Reg ("TLBEntry09", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry09" !reg);
      (Sail_impl_base.Reg ("TLBEntry10", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry10" !reg);
      (Sail_impl_base.Reg ("TLBEntry11", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry11" !reg);
      (Sail_impl_base.Reg ("TLBEntry12", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry12" !reg);
      (Sail_impl_base.Reg ("TLBEntry13", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry13" !reg);
      (Sail_impl_base.Reg ("TLBEntry14", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry14" !reg);
      (Sail_impl_base.Reg ("TLBEntry15", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry15" !reg);
      (Sail_impl_base.Reg ("TLBEntry16", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry16" !reg);
      (Sail_impl_base.Reg ("TLBEntry17", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry17" !reg);
      (Sail_impl_base.Reg ("TLBEntry18", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry18" !reg);
      (Sail_impl_base.Reg ("TLBEntry19", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry19" !reg);
      (Sail_impl_base.Reg ("TLBEntry20", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry20" !reg);
      (Sail_impl_base.Reg ("TLBEntry21", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry21" !reg);
      (Sail_impl_base.Reg ("TLBEntry22", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry22" !reg);
      (Sail_impl_base.Reg ("TLBEntry23", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry23" !reg);
      (Sail_impl_base.Reg ("TLBEntry24", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry24" !reg);
      (Sail_impl_base.Reg ("TLBEntry25", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry25" !reg);
      (Sail_impl_base.Reg ("TLBEntry26", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry26" !reg);
      (Sail_impl_base.Reg ("TLBEntry27", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry27" !reg);
      (Sail_impl_base.Reg ("TLBEntry28", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry28" !reg);
      (Sail_impl_base.Reg ("TLBEntry29", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry29" !reg);
      (Sail_impl_base.Reg ("TLBEntry30", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry30" !reg);
      (Sail_impl_base.Reg ("TLBEntry31", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry31" !reg);
      (Sail_impl_base.Reg ("TLBEntry32", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry32" !reg);
      (Sail_impl_base.Reg ("TLBEntry33", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry33" !reg);
      (Sail_impl_base.Reg ("TLBEntry34", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry34" !reg);
      (Sail_impl_base.Reg ("TLBEntry35", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry35" !reg);
      (Sail_impl_base.Reg ("TLBEntry36", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry36" !reg);
      (Sail_impl_base.Reg ("TLBEntry37", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry37" !reg);
      (Sail_impl_base.Reg ("TLBEntry38", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry38" !reg);
      (Sail_impl_base.Reg ("TLBEntry39", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry39" !reg);
      (Sail_impl_base.Reg ("TLBEntry40", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry40" !reg);
      (Sail_impl_base.Reg ("TLBEntry41", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry41" !reg);
      (Sail_impl_base.Reg ("TLBEntry42", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry42" !reg);
      (Sail_impl_base.Reg ("TLBEntry43", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry43" !reg);
      (Sail_impl_base.Reg ("TLBEntry44", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry44" !reg);
      (Sail_impl_base.Reg ("TLBEntry45", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry45" !reg);
      (Sail_impl_base.Reg ("TLBEntry46", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry46" !reg);
      (Sail_impl_base.Reg ("TLBEntry47", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry47" !reg);
      (Sail_impl_base.Reg ("TLBEntry48", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry48" !reg);
      (Sail_impl_base.Reg ("TLBEntry49", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry49" !reg);
      (Sail_impl_base.Reg ("TLBEntry50", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry50" !reg);
      (Sail_impl_base.Reg ("TLBEntry51", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry51" !reg);
      (Sail_impl_base.Reg ("TLBEntry52", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry52" !reg);
      (Sail_impl_base.Reg ("TLBEntry53", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry53" !reg);
      (Sail_impl_base.Reg ("TLBEntry54", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry54" !reg);
      (Sail_impl_base.Reg ("TLBEntry55", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry55" !reg);
      (Sail_impl_base.Reg ("TLBEntry56", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry56" !reg);
      (Sail_impl_base.Reg ("TLBEntry57", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry57" !reg);
      (Sail_impl_base.Reg ("TLBEntry58", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry58" !reg);
      (Sail_impl_base.Reg ("TLBEntry59", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry59" !reg);
      (Sail_impl_base.Reg ("TLBEntry60", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry60" !reg);
      (Sail_impl_base.Reg ("TLBEntry61", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry61" !reg);
      (Sail_impl_base.Reg ("TLBEntry62", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry62" !reg);
      (Sail_impl_base.Reg ("TLBEntry63", 116, 117, Sail_impl_base.D_decreasing), Reg.find "TLBEntry63" !reg);
    ]

let get_opcode pc_a =
  List.map
    (fun b -> match b with Some b -> b | None -> failwith "A byte in opcode contained unknown or undef")
    (List.map byte_of_memory_byte
       [
         Mem.find pc_a !prog_mem;
         Mem.find (add1 pc_a) !prog_mem;
         Mem.find (add1 (add1 pc_a)) !prog_mem;
         Mem.find (add1 (add1 (add1 pc_a))) !prog_mem;
       ]
    )

let rec write_events = function
  | [] -> ()
  | e :: events ->
      ( match e with
      | E_write_reg (Reg (id, _, _, _), value) -> reg := Reg.add id value !reg
      | E_write_reg ((Reg_slice (id, _, _, range) as reg_n), value)
      | E_write_reg ((Reg_field (id, _, _, _, range) as reg_n), value) ->
          let old_val = Reg.find id !reg in
          let new_val = fupdate_slice reg_n old_val value range in
          reg := Reg.add id new_val !reg
      | E_write_reg ((Reg_f_slice (id, _, _, _, range, mini_range) as reg_n), value) ->
          let old_val = Reg.find id !reg in
          let new_val = fupdate_slice reg_n old_val value (combine_slices range mini_range) in
          reg := Reg.add id new_val !reg
      | _ -> failwith "Only register write events expected"
      );
      write_events events

let fetch_instruction_opcode_and_update_ia model addr_trans =
  match model with
  | PPC -> (
      let cia = Reg.find "CIA" !reg in
      let cia_addr = address_of_register_value cia in
      match cia_addr with
      | Some cia_addr ->
          let cia_a = integer_of_address cia_addr in
          let opcode = get_opcode cia_a in
          begin
            reg := Reg.add "CIA" (Reg.find "NIA" !reg) !reg;
            Opcode opcode
          end
      | None -> failwith "CIA address contains unknown or undefined"
    )
  | AArch64 -> (
      let pc = Reg.find "_PC" !reg in
      let pc_addr = address_of_register_value pc in
      match pc_addr with
      | Some pc_addr ->
          let pc_a = integer_of_address pc_addr in
          let opcode = get_opcode pc_a in
          Opcode opcode
      | None -> failwith "_PC address contains unknown or undefined"
    )
  | MIPS -> begin
      let nextPC = Reg.find "nextPC" !reg in
      let pc_addr = address_of_register_value nextPC in
      (*let unused = interactf "PC: %s\n" (Printing_functions.register_value_to_string nextPC) in*)
      match pc_addr with
      | Some pc_addr ->
          let pc_a =
            match addr_trans (get_addr_trans_regs ()) pc_addr with
            | Some a, Some events ->
                write_events (List.rev events);
                integer_of_address a
            | Some a, None -> integer_of_address a
            | None, Some events -> (
                write_events (List.rev events);
                let nextPC = Reg.find "nextPC" !reg in
                let pc_addr = address_of_register_value nextPC in
                match pc_addr with
                | Some pc_addr -> (
                    match addr_trans (get_addr_trans_regs ()) pc_addr with
                    | Some a, Some events ->
                        write_events (List.rev events);
                        integer_of_address a
                    | Some a, None -> integer_of_address a
                    | None, _ -> failwith "Address translation failed twice"
                  )
                | None -> failwith "no nextPc address"
              )
            | _ -> failwith "No address and no events from translate address"
          in
          let opcode = get_opcode pc_a in
          begin
            reg := Reg.add "PC" (Reg.find "nextPC" !reg) !reg;
            Opcode opcode
          end
      | None ->
          errorf "nextPC contains unknown or undefined";
          exit 1
    end
  | _ -> assert false

let get_pc_address = function MIPS -> Reg.find "PC" !reg | PPC -> Reg.find "CIA" !reg | AArch64 -> Reg.find "_PC" !reg

let option_int_of_reg str = option_int_of_option_integer (integer_of_register_value (Reg.find str !reg))

let rec fde_loop count context model mode track_dependencies addr_trans =
  if !max_cut_off && count = !max_instr then
    resultf "\nEnding evaluation due to reaching cut off point of %d instructions\n" count
  else begin
    if !break_point && count = !break_instr then begin
      break_point := false;
      eager_eval := false
    end;
    let pc_regval = get_pc_address model in
    interactf "\n**** instruction %d from address %s ****\n" count
      (Printing_functions.register_value_to_string pc_regval);
    let pc_addr = address_of_register_value pc_regval in
    let pc_val = match pc_addr with Some v -> v | None -> failwith "pc contains undef or unknown" in
    let m_paddr_int =
      match addr_trans (get_addr_trans_regs ()) pc_val with
      | Some a, Some events ->
          write_events (List.rev events);
          Some (integer_of_address a)
      | Some a, None -> Some (integer_of_address a)
      | None, Some events ->
          write_events (List.rev events);
          None
      | None, None -> failwith "address translation failed and no writes"
    in
    match m_paddr_int with
    | Some pc ->
        let inBranchDelay = option_int_of_reg "inBranchDelay" in
        ( match inBranchDelay with
        | Some 0 ->
            let npc_addr = add_address_nat pc_val 4 in
            let npc_reg = register_value_of_address npc_addr Sail_impl_base.D_decreasing in
            reg := Reg.add "nextPC" npc_reg !reg
        | Some 1 -> reg := Reg.add "nextPC" (Reg.find "delayedPC" !reg) !reg
        | _ -> failwith "invalid value of inBranchDelay"
        );
        let opcode = Opcode (get_opcode pc) in
        let instruction, istate =
          match Interp_inter_imp.decode_to_istate context None opcode with
          | Instr (instruction, istate) ->
              let instruction = interp_value_to_instr_external context instruction in
              interactf "\n**** Running: %s ****\n" (Printing_functions.instruction_to_string instruction);
              (instruction, istate)
          | Decode_error d ->
              ( match d with
              | Interp_interface.Unsupported_instruction_error instruction ->
                  let instruction = interp_value_to_instr_external context instruction in
                  errorf "\n**** Encountered unsupported instruction %s ****\n"
                    (Printing_functions.instruction_to_string instruction)
              | Interp_interface.Not_an_instruction_error op -> (
                  match op with
                  | Opcode bytes ->
                      errorf "\n**** Encountered non-decodeable opcode: %s ****\n"
                        (Printing_functions.byte_list_to_string bytes)
                )
              | Internal_error s -> errorf "\n**** Internal error on decode: %s ****\n" s
              );
              exit 1
        in
        if stop_condition_met model instruction then
          resultf "\nSUCCESS program terminated after %d instructions\n" count
        else begin
          match
            Run_interp_model.run istate !reg !prog_mem !tag_mem (Nat_big_num.of_int 1) !eager_eval track_dependencies
              mode "execute"
          with
          | false, _, _, _ ->
              errorf "FAILURE\n";
              exit 1
          | true, mode, track_dependencies, (my_reg, my_mem, my_tags) ->
              reg := my_reg;
              prog_mem := my_mem;
              tag_mem := my_tags;

              ( try
                  let pending, _, _ = Unix.select [Unix.stdin] [] [] 0.0 in
                  if pending != [] then (
                    let char = input_byte stdin in
                    errorf "Input %x\n" char;
                    input_buf := !input_buf @ [char]
                  )
                with _ -> ()
              );

              let uart_rvalid = option_int_of_reg "UART_RVALID" in
              ( match uart_rvalid with
              | Some 0 -> (
                  match !input_buf with
                  | x :: xs ->
                      reg :=
                        Reg.add "UART_RDATA"
                          (register_value_of_integer 8 7 Sail_impl_base.D_decreasing (Nat_big_num.of_int x))
                          !reg;
                      reg :=
                        Reg.add "UART_RVALID"
                          (register_value_of_integer 1 0 Sail_impl_base.D_decreasing (Nat_big_num.of_int 1))
                          !reg;
                      input_buf := xs
                  | [] -> ()
                )
              | _ -> ()
              );

              let uart_written = option_int_of_reg "UART_WRITTEN" in
              ( match uart_written with
              | Some 1 -> (
                  let uart_data = option_int_of_reg "UART_WDATA" in
                  match uart_data with
                  | Some b ->
                      printf "%c" (Char.chr b);
                      printf "%!"
                  | None ->
                      errorf "UART_WDATA was undef";
                      exit 1
                )
              | _ -> ()
              );
              reg :=
                Reg.add "UART_WRITTEN" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero) !reg;

              reg := Reg.add "inBranchDelay" (Reg.find "branchPending" !reg) !reg;
              reg :=
                Reg.add "branchPending"
                  (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero)
                  !reg;
              reg := Reg.add "PC" (Reg.find "nextPC" !reg) !reg;
              fde_loop (count + 1) context model (Some mode) (ref track_dependencies) addr_trans
        end
    | None -> begin
        reg := Reg.add "inBranchDelay" (Reg.find "branchPending" !reg) !reg;
        reg := Reg.add "branchPending" (register_value_of_integer 1 0 Sail_impl_base.D_decreasing Nat_big_num.zero) !reg;
        reg := Reg.add "PC" (Reg.find "nextPC" !reg) !reg;
        fde_loop (count + 1) context model mode track_dependencies addr_trans
      end
  end

let rec load_raw_file' mem addr chan =
  let byte = input_byte chan in
  add_mem byte addr mem;
  load_raw_file' mem (Nat_big_num.succ addr) chan

let rec load_raw_file mem addr chan = try load_raw_file' mem addr chan with End_of_file -> ()

let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "";
  if !file = "" then begin
    Arg.usage args "";
    exit 1
  end;
  if !break_point then eager_eval := true;

  let ( ( isa_defs,
          (isa_m0, isa_m1, isa_m2, isa_m3, isa_m4),
          isa_externs,
          isa_model,
          model_reg_d,
          startaddr,
          startaddr_internal
        ),
        pp_symbol_map ) =
    initial_system_state_of_elf_file !file
  in

  let context = build_context false isa_defs isa_m0 [] isa_m1 isa_m2 isa_m3 [] isa_m4 None isa_externs in
  (*NOTE: this is likely MIPS specific, so should probably pull from initial_system_state info on to translate or not,
          endian mode, and translate function name
  *)
  let addr_trans = translate_address context E_little_endian "TranslatePC" in
  if String.length !raw_file != 0 then load_raw_file prog_mem (Nat_big_num.of_int !raw_at) (open_in_bin !raw_file);
  reg := Reg.add "PC" (register_value_of_address startaddr_internal model_reg_d) !reg;
  (* entry point: unit -> unit fde *)
  let name = Filename.basename !file in
  let t = time_it (fun () -> fde_loop 0 context isa_model (Some Run) (ref false) addr_trans) () in
  resultf "Execution time for file %s: %f seconds\n" name t
;;

(* Turn off line-buffering of standard input to allow responsive console input *)
if Unix.isatty Unix.stdin then begin
  let tattrs = Unix.tcgetattr Unix.stdin in
  Unix.tcsetattr Unix.stdin Unix.TCSANOW { tattrs with c_icanon = false }
end
;;

run ()
