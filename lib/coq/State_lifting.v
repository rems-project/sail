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

Require Import Sail.Values.
Require Import Sail.Prompt_monad.
Require Import Sail.Prompt.
Require Import Sail.State_monad.
Import ListNotations.

(* Lifting from prompt monad to state monad *)
(*val liftState : forall 'regval 'regs 'a 'e. register_accessors 'regs 'regval -> monad 'regval 'a 'e -> monadS 'regs 'a 'e*)
Fixpoint liftState {Regval Regs A E} (ra : register_accessors Regs Regval) (m : monad Regval A E) : monadS Regs A E :=
 match m with
  | (Done a)                   => returnS a
  | (Read_mem rk a sz k)       => bindS (read_mem_bytesS rk a sz)       (fun v => liftState ra (k v))
  | (Read_memt rk a sz k)      => bindS (read_memt_bytesS rk a sz)      (fun v => liftState ra (k v))
  | (Write_mem wk a sz v k)    => bindS (write_mem_bytesS wk a sz v)    (fun v => liftState ra (k v))
  | (Write_memt wk a sz v t k) => bindS (write_memt_bytesS wk a sz v t) (fun v => liftState ra (k v))
  | (Write_tag wk a t k)       => bindS (write_tag_rawS wk a t)         (fun v => liftState ra (k v))
  | (Read_reg r k)             => bindS (read_regvalS ra r)             (fun v => liftState ra (k v))
  | (Excl_res k)               => bindS (excl_resultS tt)               (fun v => liftState ra (k v))
  | (Choose _ ty k)            => bindS (chooseS ty)                    (fun v => liftState ra (k v))
  | (Write_reg r v k)          => seqS (write_regvalS ra r v)           (liftState ra k)
  | (Write_ea _ _ _ k)         => liftState ra k
  | (Footprint k)              => liftState ra k
  | (Barrier _ k)              => liftState ra k
  | (Print _ k)                => liftState ra k (* TODO *)
  | (Fail descr)               => failS descr
  | (Exception e)              => throwS e
end.

Local Open Scope bool_scope.

(*val emitEventS : forall 'regval 'regs 'a 'e. Eq 'regval => register_accessors 'regs 'regval -> event 'regval -> sequential_state 'regs -> maybe (sequential_state 'regs)*)
Definition emitEventS {Regval Regs} `{forall (x y : Regval), Decidable (x = y)} (ra : register_accessors Regs Regval) (e : event Regval) (s : sequential_state Regs) : option (sequential_state Regs) :=
match e with
  | E_read_mem _ addr sz v =>
     option_bind (get_mem_bytes addr sz s) (fun '(v', _) =>
     if generic_eq v' v then Some s else None)
  | E_read_memt _ addr sz (v, tag) =>
     option_bind (get_mem_bytes addr sz s) (fun '(v', tag') =>
     if generic_eq v' v && generic_eq tag' tag then Some s else None)
  | E_write_mem _ addr sz v success =>
     if success then Some (put_mem_bytes addr sz v B0 s) else None
  | E_write_memt _ addr sz v tag success =>
     if success then Some (put_mem_bytes addr sz v tag s) else None
  | E_write_tag _ addr sz tag success =>
     if success then Some (put_tag addr tag s) else None
  | E_read_reg r v =>
     let (read_reg, _) := ra in
     option_bind (read_reg r s.(ss_regstate)) (fun v' =>
     if generic_eq v' v then Some s else None)
  | E_write_reg r v =>
     let (_, write_reg) := ra in
     option_bind (write_reg r v s.(ss_regstate)) (fun rs' =>
     Some {| ss_regstate := rs'; ss_memstate := s.(ss_memstate); ss_tagstate := s.(ss_tagstate) |})
  | _ => Some s
end.

Local Close Scope bool_scope.

(*val runTraceS : forall 'regval 'regs 'a 'e. Eq 'regval => register_accessors 'regs 'regval -> trace 'regval -> sequential_state 'regs -> maybe (sequential_state 'regs)*)
Fixpoint runTraceS {Regval Regs} `{forall (x y : Regval), Decidable (x = y)} (ra : register_accessors Regs Regval) (t : trace Regval) (s : sequential_state Regs) : option (sequential_state Regs) :=
match t with
  | [] => Some s
  | e :: t' => option_bind (emitEventS ra e s) (runTraceS ra t')
end.
