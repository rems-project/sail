(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Shaked Flur                                   *)
(*  Copyright (c) 2015-2017 Kathyrn Gray                                  *)
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
(*========================================================================*)

register alias PSTATE_N   = NZCV.N  (* Negative condition flag *)
register alias PSTATE_Z   = NZCV.Z  (* Zero condition flag *)
register alias PSTATE_C   = NZCV.C  (* Carry condition flag *)
register alias PSTATE_V   = NZCV.V  (* oVerflow condition flag *)
register alias PSTATE_D   = DAIF.D  (* Debug mask bit                     [AArch64 only] *)
register alias PSTATE_A   = DAIF.A  (* Asynchronous abort mask bit *)
register alias PSTATE_I   = DAIF.I  (* IRQ mask bit *)
register alias PSTATE_F   = DAIF.F  (* FIQ mask bit *)
(* register alias PSTATE_SS  =         (* Software step bit *) *)
(* register alias PSTATE_IL  =         (* Illegal execution state bit *) *)
register alias PSTATE_EL  = CurrentEL.EL (* Exception Level *)
register (bit[1]) PSTATE_nRW           (* not Register Width: 0=64, 1=32 *)
register alias PSTATE_SP = SPSel.SP (* Stack pointer select: 0=SP0, 1=SPx [AArch64 only] *) (* TODO: confirm this *)
(* register alias PSTATE_Q   =         (* Cumulative saturation flag         [AArch32 only] *) *)
(* register alias PSTATE_GE  =         (* Greater than or Equal flags        [AArch32 only] *) *)
(* register alias PSTATE_IT  =         (* If-then bits, RES0 in CPSR         [AArch32 only] *) *)
(* register alias PSTATE_J   =         (* J bit, RES0 in CPSR                [AArch32 only, RES0 in ARMv8] *) *)
(* register alias PSTATE_T   =         (* T32 bit, RES0 in CPSR              [AArch32 only] *) *)
register (bit[1]) PSTATE_E             (* Endianness bit                     [AArch32 only] *)
register (bit[5]) PSTATE_M          (* Mode field                         [AArch32 only] *)


(* this is a convenient way to do "PSTATE.<N,Z,C,V> = nzcv;" *)
function unit effect {wreg} wPSTATE_NZCV((), [n,z,c,v]) =
{
  PSTATE_N := n;
  PSTATE_Z := z;
  PSTATE_C := c;
  PSTATE_V := v;
}

(* this is a convenient way to do "PSTATE.<D,A,I,F> = daif;" *)
function unit effect {wreg} wPSTATE_DAIF((), [d,a,i,f]) =
{
  PSTATE_D := d;
  PSTATE_A := a;
  PSTATE_I := i;
  PSTATE_F := f;
}
