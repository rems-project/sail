(*==========================================================================*)
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
(*==========================================================================*)

Require Import DecidableClass.

Class EnumerationType (A : Type) := {
  toNat : A -> nat
}.

(*
val enumeration_typeCompare : forall 'a. EnumerationType 'a => 'a -> 'a -> ordering
let ~{ocaml} enumeration_typeCompare e1 e2 :=
  compare (toNat e1) (toNat e2)
let inline {ocaml} enumeration_typeCompare := defaultCompare


default_instance forall 'a. EnumerationType 'a => (Ord 'a)
  let compare := enumeration_typeCompare
  let (<)  r1 r2 := (enumeration_typeCompare r1 r2) = LT
  let (<=) r1 r2 := (enumeration_typeCompare r1 r2) <> GT
  let (>)  r1 r2 := (enumeration_typeCompare r1 r2) = GT
  let (>=) r1 r2 := (enumeration_typeCompare r1 r2) <> LT
end
*)

(* Data structures for building up instructions *)

(* careful: changes in the read/write/barrier kinds have to be
   reflected in deep_shallow_convert *)
Inductive read_kind :=
  (* common reads *)
  | Read_plain
  (* Power reads *)
  | Read_reserve
  (* AArch64 reads *)
  | Read_acquire | Read_exclusive | Read_exclusive_acquire | Read_stream
  (* RISC-V reads *)
  | Read_RISCV_acquire  | Read_RISCV_strong_acquire
  | Read_RISCV_reserved | Read_RISCV_reserved_acquire
  | Read_RISCV_reserved_strong_acquire
  (* x86 reads *)
  | Read_X86_locked (* the read part of a lock'd instruction (rmw) *)
  (* instruction fetch *)
  | Read_ifetch
.
Scheme Equality for read_kind.
(*
instance (Show read_kind)
  let show := function
    | Read_plain -> "Read_plain"
    | Read_reserve -> "Read_reserve"
    | Read_acquire -> "Read_acquire"
    | Read_exclusive -> "Read_exclusive"
    | Read_exclusive_acquire -> "Read_exclusive_acquire"
    | Read_stream -> "Read_stream"
    | Read_RISCV_acquire -> "Read_RISCV_acquire"
    | Read_RISCV_strong_acquire -> "Read_RISCV_strong_acquire"
    | Read_RISCV_reserved -> "Read_RISCV_reserved"
    | Read_RISCV_reserved_acquire -> "Read_RISCV_reserved_acquire"
    | Read_RISCV_reserved_strong_acquire -> "Read_RISCV_reserved_strong_acquire"
    | Read_X86_locked -> "Read_X86_locked"
    | Read_ifetch -> "Read_ifetch"
  end
end
*)
Inductive write_kind :=
  (* common writes *)
  | Write_plain
  (* Power writes *)
  | Write_conditional
  (* AArch64 writes *)
  | Write_release | Write_exclusive | Write_exclusive_release
  (* RISC-V *)
  | Write_RISCV_release     | Write_RISCV_strong_release
  | Write_RISCV_conditional | Write_RISCV_conditional_release
  | Write_RISCV_conditional_strong_release
  (* x86 writes *)
  | Write_X86_locked (* the write part of a lock'd instruction (rmw) *)
.
Scheme Equality for write_kind.
(*
instance (Show write_kind)
  let show := function
    | Write_plain -> "Write_plain"
    | Write_conditional -> "Write_conditional"
    | Write_release -> "Write_release"
    | Write_exclusive -> "Write_exclusive"
    | Write_exclusive_release -> "Write_exclusive_release"
    | Write_RISCV_release -> "Write_RISCV_release"
    | Write_RISCV_strong_release -> "Write_RISCV_strong_release"
    | Write_RISCV_conditional -> "Write_RISCV_conditional"
    | Write_RISCV_conditional_release -> "Write_RISCV_conditional_release"
    | Write_RISCV_conditional_strong_release -> "Write_RISCV_conditional_strong_release"
    | Write_X86_locked -> "Write_X86_locked"
  end
end
*)

Inductive a64_barrier_domain :=
  A64_FullShare
  | A64_InnerShare
  | A64_OuterShare
  | A64_NonShare.
Scheme Equality for a64_barrier_domain.

Inductive a64_barrier_type :=
  A64_barrier_all
  | A64_barrier_LD
  | A64_barrier_ST.
Scheme Equality for a64_barrier_type.

Inductive barrier_kind :=
  (* Power barriers *)
  | Barrier_Sync : unit -> barrier_kind
  | Barrier_LwSync : unit -> barrier_kind
  | Barrier_Eieio : unit -> barrier_kind
  | Barrier_Isync : unit -> barrier_kind
  (* AArch64 barriers *)
  | Barrier_DMB : a64_barrier_domain * a64_barrier_type -> barrier_kind
  | Barrier_DSB : a64_barrier_domain * a64_barrier_type -> barrier_kind
  | Barrier_ISB : unit -> barrier_kind
 (* | Barrier_TM_COMMIT*)
  (* MIPS barriers *)
  | Barrier_MIPS_SYNC : unit -> barrier_kind
  (* RISC-V barriers *)
  | Barrier_RISCV_rw_rw : unit -> barrier_kind
  | Barrier_RISCV_r_rw : unit -> barrier_kind
  | Barrier_RISCV_r_r : unit -> barrier_kind
  | Barrier_RISCV_rw_w : unit -> barrier_kind
  | Barrier_RISCV_w_w : unit -> barrier_kind
  | Barrier_RISCV_w_rw : unit -> barrier_kind
  | Barrier_RISCV_rw_r : unit -> barrier_kind
  | Barrier_RISCV_r_w : unit -> barrier_kind
  | Barrier_RISCV_w_r : unit -> barrier_kind
  | Barrier_RISCV_tso : unit -> barrier_kind
  | Barrier_RISCV_i : unit -> barrier_kind
  (* X86 *)
  | Barrier_x86_MFENCE : unit -> barrier_kind.
(* Doesn't work for *  Scheme Equality for barrier_kind.*)
Definition barrier_kind_beq x y :=
match x, y with
  | Barrier_Sync _, Barrier_Sync _ => true
  | Barrier_LwSync _, Barrier_LwSync _ => true
  | Barrier_Eieio _, Barrier_Eieio _ => true
  | Barrier_Isync _, Barrier_Isync _ => true
  (* AArch64 barriers *)
  | Barrier_DMB (d, t), Barrier_DMB (d', t') => andb (a64_barrier_domain_beq d d') (a64_barrier_type_beq t t')
  | Barrier_DSB (d, t), Barrier_DSB (d', t') => andb (a64_barrier_domain_beq d d') (a64_barrier_type_beq t t')
  | Barrier_ISB _, Barrier_ISB _ => true
 (* | Barrier_TM_COMMIT*)
  (* MIPS barriers *)
  | Barrier_MIPS_SYNC _, Barrier_MIPS_SYNC _ => true
  (* RISC-V barriers *)
  | Barrier_RISCV_rw_rw _, Barrier_RISCV_rw_rw _ => true
  | Barrier_RISCV_r_rw _, Barrier_RISCV_r_rw _ => true
  | Barrier_RISCV_r_r _, Barrier_RISCV_r_r _ => true
  | Barrier_RISCV_rw_w _, Barrier_RISCV_rw_w _ => true
  | Barrier_RISCV_w_w _, Barrier_RISCV_w_w _ => true
  | Barrier_RISCV_w_rw _, Barrier_RISCV_w_rw _ => true
  | Barrier_RISCV_rw_r _, Barrier_RISCV_rw_r _ => true
  | Barrier_RISCV_r_w _, Barrier_RISCV_r_w _ => true
  | Barrier_RISCV_w_r _, Barrier_RISCV_w_r _ => true
  | Barrier_RISCV_tso _, Barrier_RISCV_tso _ => true
  | Barrier_RISCV_i _, Barrier_RISCV_i _ => true
  (* X86 *)
  | Barrier_x86_MFENCE _, Barrier_x86_MFENCE _ => true
  | _, _ => false
end.


(*
instance (Show barrier_kind)
  let show := function
    | Barrier_Sync -> "Barrier_Sync"
    | Barrier_LwSync -> "Barrier_LwSync"
    | Barrier_Eieio -> "Barrier_Eieio"
    | Barrier_Isync -> "Barrier_Isync"
    | Barrier_DMB -> "Barrier_DMB"
    | Barrier_DMB_ST -> "Barrier_DMB_ST"
    | Barrier_DMB_LD -> "Barrier_DMB_LD"
    | Barrier_DSB -> "Barrier_DSB"
    | Barrier_DSB_ST -> "Barrier_DSB_ST"
    | Barrier_DSB_LD -> "Barrier_DSB_LD"
    | Barrier_ISB -> "Barrier_ISB"
    | Barrier_TM_COMMIT -> "Barrier_TM_COMMIT"
    | Barrier_MIPS_SYNC -> "Barrier_MIPS_SYNC"
    | Barrier_RISCV_rw_rw -> "Barrier_RISCV_rw_rw"
    | Barrier_RISCV_r_rw  -> "Barrier_RISCV_r_rw"
    | Barrier_RISCV_r_r   -> "Barrier_RISCV_r_r"
    | Barrier_RISCV_rw_w  -> "Barrier_RISCV_rw_w"
    | Barrier_RISCV_w_w   -> "Barrier_RISCV_w_w"
    | Barrier_RISCV_w_rw  -> "Barrier_RISCV_w_rw"
    | Barrier_RISCV_rw_r  -> "Barrier_RISCV_rw_r"
    | Barrier_RISCV_r_w   -> "Barrier_RISCV_r_w"
    | Barrier_RISCV_w_r   -> "Barrier_RISCV_w_r"
    | Barrier_RISCV_tso   -> "Barrier_RISCV_tso"
    | Barrier_RISCV_i     -> "Barrier_RISCV_i"
    | Barrier_x86_MFENCE  -> "Barrier_x86_MFENCE"
  end
end*)

Inductive trans_kind :=
  (* AArch64 *)
  | Transaction_start | Transaction_commit | Transaction_abort.
Scheme Equality for trans_kind.
(*
instance (Show trans_kind)
  let show := function
  | Transaction_start  -> "Transaction_start"
  | Transaction_commit -> "Transaction_commit"
  | Transaction_abort  -> "Transaction_abort"
  end
end*)

(* cache maintenance instructions *)
Inductive cache_op_kind :=
  (* AArch64 DC *)
  | Cache_op_D_IVAC | Cache_op_D_ISW  | Cache_op_D_CSW  |  Cache_op_D_CISW
  | Cache_op_D_ZVA  | Cache_op_D_CVAC | Cache_op_D_CVAU | Cache_op_D_CIVAC
  (* AArch64 IC *)
  | Cache_op_I_IALLUIS | Cache_op_I_IALLU | Cache_op_I_IVAU
.
Scheme Equality for cache_op_kind.

Inductive instruction_kind :=
  | IK_barrier   : barrier_kind -> instruction_kind
  | IK_mem_read  : read_kind -> instruction_kind
  | IK_mem_write : write_kind -> instruction_kind
  | IK_mem_rmw   : (read_kind * write_kind) -> instruction_kind
  | IK_branch    : unit -> instruction_kind (* this includes conditional-branch (multiple nias, none of which is NIA_indirect_address),
  indirect/computed-branch (single nia of kind NIA_indirect_address)
  and branch/jump (single nia of kind NIA_concrete_address) *)
  | IK_trans     : trans_kind -> instruction_kind
  | IK_simple    : unit -> instruction_kind
  | IK_cache_op  : cache_op_kind -> instruction_kind
.

(*
instance (Show instruction_kind)
  let show := function
    | IK_barrier barrier_kind -> "IK_barrier " ^ (show barrier_kind)
    | IK_mem_read read_kind   -> "IK_mem_read " ^ (show read_kind)
    | IK_mem_write write_kind -> "IK_mem_write " ^ (show write_kind)
    | IK_mem_rmw (r, w)       -> "IK_mem_rmw " ^ (show r) ^ " " ^ (show w)
    | IK_branch               -> "IK_branch"
    | IK_trans trans_kind     -> "IK_trans " ^ (show trans_kind)
    | IK_simple               -> "IK_simple"
  end
end
*)

Definition read_is_exclusive r :=
match r with
  | Read_plain => false
  | Read_reserve => true
  | Read_acquire => false
  | Read_exclusive => true
  | Read_exclusive_acquire => true
  | Read_stream => false
  | Read_RISCV_acquire => false
  | Read_RISCV_strong_acquire => false
  | Read_RISCV_reserved => true
  | Read_RISCV_reserved_acquire => true
  | Read_RISCV_reserved_strong_acquire => true
  | Read_X86_locked => true
  | Read_ifetch => false
end.


(*
instance (EnumerationType read_kind)
  let toNat := function
    | Read_plain -> 0
    | Read_reserve -> 1
    | Read_acquire -> 2
    | Read_exclusive -> 3
    | Read_exclusive_acquire -> 4
    | Read_stream -> 5
    | Read_RISCV_acquire -> 6
    | Read_RISCV_strong_acquire -> 7
    | Read_RISCV_reserved -> 8
    | Read_RISCV_reserved_acquire -> 9
    | Read_RISCV_reserved_strong_acquire -> 10
    | Read_X86_locked -> 11
    | Read_ifetch -> 12
  end
end

instance (EnumerationType write_kind)
  let toNat := function
    | Write_plain -> 0
    | Write_conditional -> 1
    | Write_release -> 2
    | Write_exclusive -> 3
    | Write_exclusive_release -> 4
    | Write_RISCV_release -> 5
    | Write_RISCV_strong_release -> 6
    | Write_RISCV_conditional -> 7
    | Write_RISCV_conditional_release -> 8
    | Write_RISCV_conditional_strong_release -> 9
    | Write_X86_locked -> 10
  end
end

instance (EnumerationType barrier_kind)
  let toNat := function
    | Barrier_Sync -> 0
    | Barrier_LwSync -> 1
    | Barrier_Eieio ->2
    | Barrier_Isync -> 3
    | Barrier_DMB -> 4
    | Barrier_DMB_ST -> 5
    | Barrier_DMB_LD -> 6
    | Barrier_DSB -> 7
    | Barrier_DSB_ST -> 8
    | Barrier_DSB_LD -> 9
    | Barrier_ISB -> 10
    | Barrier_TM_COMMIT -> 11
    | Barrier_MIPS_SYNC -> 12
    | Barrier_RISCV_rw_rw -> 13
    | Barrier_RISCV_r_rw -> 14
    | Barrier_RISCV_r_r -> 15
    | Barrier_RISCV_rw_w -> 16
    | Barrier_RISCV_w_w -> 17
    | Barrier_RISCV_w_rw -> 18
    | Barrier_RISCV_rw_r -> 19
    | Barrier_RISCV_r_w -> 20
    | Barrier_RISCV_w_r -> 21
    | Barrier_RISCV_tso -> 22
    | Barrier_RISCV_i -> 23
    | Barrier_x86_MFENCE -> 24
  end
end
*)
