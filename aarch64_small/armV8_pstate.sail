/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Shaked Flur                                   */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

/* register alias PSTATE_N   = NZCV.N  /\* Negative condition flag *\/ */
function set_PSTATE_N(v) = {NZCV.N = v}
function get_PSTATE_N() = NZCV.N
overload PSTATE_N = {set_PSTATE_N, get_PSTATE_N}

/* register alias PSTATE_Z   = NZCV.Z  /\* Zero condition flag *\/ */
function set_PSTATE_Z(v) = {NZCV.Z = v}
function get_PSTATE_Z() = NZCV.Z
overload PSTATE_Z = {set_PSTATE_Z, get_PSTATE_Z}

/* register alias PSTATE_C   = NZCV.C  /\* Carry condition flag *\/ */
function set_PSTATE_C(v) = {NZCV.C = v}
function get_PSTATE_C() = NZCV.C
overload PSTATE_C = {set_PSTATE_C, get_PSTATE_C}

/* register alias PSTATE_V   = NZCV.V  /\* oVerflow condition flag *\/ */
function set_PSTATE_V(v) = {NZCV.V = v}
function get_PSTATE_V() = NZCV.V
overload PSTATE_V = {set_PSTATE_V, get_PSTATE_V}

/* register alias PSTATE_D   = DAIF.D  /\* Debug mask bits(AArch64 only) *\/ */
function set_PSTATE_D(v) = {NZCV.D = v}
function get_PSTATE_D() = NZCV.D
overload PSTATE_D = {set_PSTATE_D, get_PSTATE_D}

/* register alias PSTATE_A   = DAIF.A  /\* Asynchronous abort mask bit *\/ */
function set_PSTATE_A(v) = {NZCV.A = v}
function get_PSTATE_A() = NZCV.A
overload PSTATE_A = {set_PSTATE_A, get_PSTATE_A}

/* register alias PSTATE_I   = DAIF.I  /\* IRQ mask bit *\/ */
function set_PSTATE_I(v) = {NZCV.I = v}
function get_PSTATE_I() = NZCV.I
overload PSTATE_I = {set_PSTATE_I, get_PSTATE_I}

/* register alias PSTATE_F   = DAIF.F  /\* FIQ mask bit *\/ */
function set_PSTATE_F(v) = {NZCV.F = v}
function get_PSTATE_F() = NZCV.F
overload PSTATE_F = {set_PSTATE_F, get_PSTATE_F}

/*    register alias PSTATE_SS  =         /* Software step bit */ */
/*    register alias PSTATE_IL  =         /* Illegal execution state bit */ */

/* register alias PSTATE_EL  = CurrentEL.EL /\* Exception Level *\/ */
function set_PSTATE_EL(v) = {NZCV.EL = v}
function get_PSTATE_EL() = NZCV.EL
overload PSTATE_EL = {set_PSTATE_EL, get_PSTATE_EL}

/* register PSTATE_nRW : bits(1)           /\* not Register Width: 0=64, 1=32 *\/ */
function set_PSTATE_nRW(v) = {NZCV.nRW = v}
function get_PSTATE_nRW() = NZCV.nRW
overload PSTATE_nRW = {set_PSTATE_nRW, get_PSTATE_nRW}

/* register alias PSTATE_SP = SPSel.SP /\* Stack pointer select: 0=SP0, 1=SPx [AArch64 only] *\/ /\* TODO: confirm this *\/ */
function set_PSTATE_SP(v) = {NZCV.SP = v}
function get_PSTATE_SP() = NZCV.SP
overload PSTATE_SP = {set_PSTATE_SP, get_PSTATE_SP}

/*    register alias PSTATE_Q   =         /* Cumulative saturation flag         [AArch32 only] */ */
/*    register alias PSTATE_GE  =         /* Greater than or Equal flags        [AArch32 only] */ */
/*    register alias PSTATE_IT  =         /* If-then bits, RES0 in CPSR         [AArch32 only] */ */
/*    register alias PSTATE_J   =         /* J bit, RES0 in CPSR                [AArch32 only, RES0 in ARMv8] */ */
/*    register alias PSTATE_T   =         /* T32 bit, RES0 in CPSR              [AArch32 only] */ */
/* register PSTATE_E : bits(1)             /\* Endianness bits(AArch32 only) *\/ */
function set_PSTATE_E(v) = {NZCV.E = v}
function get_PSTATE_E() = NZCV.E
overload PSTATE_E = {set_PSTATE_E, get_PSTATE_E}

/* register PSTATE_M : bits(5)          /\* Mode field                         [AArch32 only] *\/ */
function set_PSTATE_M(v) = {NZCV.M = v}
function get_PSTATE_M() = NZCV.M
overload PSTATE_M = {set_PSTATE_M, get_PSTATE_M}


/* this is a convenient way to do "PSTATE.<N,Z,C,V> = nzcv;" */
val wPSTATE_NZCV : (unit, bits(4)) -> unit effect {wreg}
function wPSTATE_NZCV((), [n,z,c,v]) =
{
  PSTATE_N = n;
  PSTATE_Z = z;
  PSTATE_C = c;
  PSTATE_V = v;
}

/* this is a convenient way to do "PSTATE.<D,A,I,F> = daif;" */
val wPSTATE_DAIF : (unit, bits(4)) -> unit effect {wreg}
function wPSTATE_DAIF((), [d,a,i,f]) =
{
  PSTATE_D = d;
  PSTATE_A = a;
  PSTATE_I = i;
  PSTATE_F = f;
}
