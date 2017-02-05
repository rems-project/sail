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

typedef CurrentEL_type = register bits [31:0]
{
  (*31..4 : RES0;*)
  3..2 : EL;
  (*1..0 : RES0;*)
}
register (CurrentEL_type) CurrentEL (* Current Exception Level *)

typedef DAIF_type = register bits [31:0]
{
  (*31..10 : RES0;*)
  9 : D;
  8 : A;
  7 : I;
  6 : F;
  (*5..0 : RES0;*)
}
register (DAIF_type) DAIF (* Interrupt Mask Bits *)

typedef NZCV_type = register bits [31:0]
{
  31 : N;
  30 : Z;
  29 : C;
  28 : V;
  (*27..0 : RES0;*)
}
register (NZCV_type) NZCV (* Condition Flags *)

register (bit[64]) SP_EL0 (* Stack Pointer (EL0) *)
register (bit[64]) SP_EL1 (* Stack Pointer (EL1) *)
register (bit[64]) SP_EL2 (* Stack Pointer (EL2) *)
register (bit[64]) SP_EL3 (* Stack Pointer (EL3) *)

typedef SPSel_type = register bits [31:0]
{
  (*31..1 : RES0;*)
  0 : SP;
}
register (SPSel_type) SPSel (* Stack Pointer Select *)

typedef SPSR_type = register bits [31:0]
{
  31 : N;
  30 : Z;
  29 : C;
  28 : V;
  (*27..22 : RES0;*)
  21 : SS;
  20 : IL;
  (*19..10 : RES0*)
   9 : E;
   8 : A;
   7 : I;
   6 : F;
   (*5 : RES0;*)
   4 : M4;
   3..0 : M3_0;
}
register (SPSR_type) SPSR_EL1 (* Saved Program Status Register (EL1) *)
register (SPSR_type) SPSR_EL2 (* Saved Program Status Register (EL2) *)
register (SPSR_type) SPSR_EL3 (* Saved Program Status Register (EL3) *)


register (bit[64]) ELR_EL1 (* Exception Link Register (EL1) *)
register (bit[64]) ELR_EL2 (* Exception Link Register (EL2) *)
register (bit[64]) ELR_EL3 (* Exception Link Register (EL3) *)

