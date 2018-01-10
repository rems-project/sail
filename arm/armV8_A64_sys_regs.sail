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

(*************************************************************************)
(* General system control registers *)


typedef HCR_type = register bits [63:0]
{
  (*63..34 : RES0;*)
  33 : ID;
  32 : CD;
  31 : RW;
  30 : TRVM;
  29 : HCD;
  28 : TDZ;
  27 : TGE;
  26 : TVM;
  25 : TTLB;
  24 : TPU;
  23 : TPC;
  22 : TSW;
  21 : TACR;
  20 : TIDCP;
  19 : TSC;
  18 : TID3;
  17 : TID2;
  16 : TID1;
  15 : TID0;
  14 : TWE;
  13 : TWI;
  12 : DC;
  11..10 :BSU;
  9  : FB;
  8  : VSE;
  7  : VI;
  6  : VF;
  5  : AMO;
  4  : IMO;
  3  : FMO;
  2  : PTW;
  1  : SWIO;
  0  : VM;
}
register (HCR_type) HCR_EL2 (* Hypervisor Configuration Register *)


typedef ID_AA64MMFR0_type = register bits [63:0]
{
  (*63..32 : RES0;*)
  31..28 : TGran4;
  27..24 : TGran64;
  23..20 : TGran16;
  19..16 : BigEndEL0;
  15..12 : SNSMem;
  11..8  : BigEnd;
   7..4  : ASIDBits;
   3..0  : PARange;
}
register (ID_AA64MMFR0_type) ID_AA64MMFR0_EL1 (* AArch64 Memory Model Feature Register 0 *)

register (bit[64]) RVBAR_EL1 (* Reset Vector Base Address Register (if EL2 and EL3 not implemented) *)
register (bit[64]) RVBAR_EL2 (* Reset Vector Base Address Register (if EL3 not implemented) *)
register (bit[64]) RVBAR_EL3 (* Reset Vector Base Address Register (if EL3 implemented) *)

typedef SCRType = register bits [31:0]
{
  (*31..14 : RES0;*)
  13 : TWE;
  12 : TWI;
  11 : ST;
  10 : RW;
  9  : SIF;
  8  : HCE;
  7  : SMD;
  (*6  : RES0;*)
  (*5..4  : RES1;*)
  3  : EA;
  2  : FIQ;
  1  : IRQ;
  0  : NS;
}
register (SCRType) SCR_EL3 (* Secure Configuration Register *)

typedef SCTLR_EL1_type = register bits [31:0]
{
  (*31..30 : RES0;*)
  (*29..28 : RES1;*)
  (*27     : RES0;*)
  26     : UCI;
  25     : EE;
  24     : E0E;
  (*23..22 : RES1;*)
  (*21     : RES0;*)
  (*20     : RES1;*)
  19     : WXN;
  18     : nTWE;
  (*17     : RES0;*)
  16     : nTWI;
  15     : UCT;
  14     : DZE;
  (*13     : RES0;*)
  12     : I;
  (*11     : RES1;*)
  (*10     : RES0;*)
  9      : UMA;
  8      : SED;
  7      : ITD;
  (*6      : RES0;*)
  5      : CP15BEN;
  4      : SA0;
  3      : SA;
  2      : C;
  1      : A;
  0      : M;
}
register (SCTLR_EL1_type) SCTLR_EL1 (* System Control Register (EL1) *)

typedef SCTLR_type = register bits [31:0]
{
  (*31..30 : RES0;*)
  (*29..28 : RES1;*)
  (*27..26 : RES0;*)
  25     : EE;
  (*24     : RES0;*)
  (*23..22 : RES1;*)
  (*21..20 : RES0;*)
  19     : WXN;
  (*18     : RES1;*)
  (*17     : RES0;*)
  (*16     : RES1;*)
  (*15..13 : RES0;*)
  12     : I;
  (*11     : RES1;*)
  (*10..6  : RES0;*)
  (*5..4   : RES1;*)
  3      : SA;
  2      : C;
  1      : A;
  0      : M;
}
register (SCTLR_type) SCTLR_EL2 (* System Control Register (EL2) *)
register (SCTLR_type) SCTLR_EL3 (* System Control Register (EL3) *)

typedef TCR_EL1_type = register bits [63:0]
{
  (*63..39 : RES0;*)
  38     : TBI1;
  37     : TBI0;
  36     : AS;
  (*35     : RES0;*)
  34..32 : IPS;
  31..30 : TG1;
  29..28 : SH1;
  27..26 : ORGN1;
  25..24 : IRGN1;
  23     : EPD1;
  22     : A1;
  21..16 : T1SZ;
  15..14 : TG0;
  13..12 : SH0;
  11..10 : ORGN0;
  9..8   : IRGN0;
  7      : EPD0;
  (*6      : RES0;*)
  5..0   : T0SZ;
}
register (TCR_EL1_type) TCR_EL1 (* Translation Control Register (EL1) *)

typedef TCR_type = register bits [31:0]
{
  (*31     : RES1;*)
  (*30..24 : RES0;*)
  (*23     : RES1;*)
  (*22..21 : RES0;*)
  20     : TBI;
  (*19     : RES0;*)
  18..16 : PS;
  15..14 : TG0;
  13..12 : SH0;
  11..10 : ORGN0;
  9..8   : IRGN0;
  (*7..6   : RES0;*)
  5..0   : T0SZ;
}
register (TCR_type) TCR_EL2 (* Translation Control Register (EL2) *)
register (TCR_type) TCR_EL3 (* Translation Control Register (EL3) *)

register (bit[64]) TPIDR_EL0 (* EL0 Read/Write Software Thread ID Register *)
register (bit[64]) TPIDR_EL1 (* EL1 Read/Write Software Thread ID Register *)
register (bit[64]) TPIDR_EL2 (* EL2 Read/Write Software Thread ID Register *)
register (bit[64]) TPIDR_EL3 (* EL3 Read/Write Software Thread ID Register *)

(*************************************************************************)
(* Debug registers *)

typedef DBGPRCR_type = register bits [31:0]
{
  (*31..1 : RES0;*)
  0 : CORENPDRQ;
}
register (DBGPRCR_type) DBGPRCR_EL1 (* Debug Power Control Register *)

typedef OSDLR_type = register bits [31:0]
{
  (*31..1 : RES0;*)
  0 : DLK;
}
register (OSDLR_type) OSDLR_EL1 (* OS Double Lock Register *)

(*************************************************************************)
(* Performance Monitors registers *)

(*************************************************************************)
(* Generic Timer registers *)

(*************************************************************************)
(* Generic Interrupt Controller CPU interface registers *)

(*************************************************************************)
(* External Debug Register *)

typedef EDSCR_type = register bits [31:0]
{
  (*31 : RES0;*)
  30 : RXfull;
  29 : TXfull;
  28 : ITO;
  27 : RXO;
  26 : TXU;
  25 : PipeAdv;
  24 : ITE;
  23..22 : INTdis;
  21 : TDA;
  20 : MA;
  (*19 : RES0;*)
  18 : NS;
  (*17 : RES0;*)
  16 : SDD;
  (*15 : RES0;*)
  14 : HDE;
  13..10 : RW;
  9..8 : EL;
  7 : A;
  6 : ERR;
  5..0 : STATUS;
}
register (EDSCR_type) EDSCR (* External Debug Status and Control Register *)

(* transactional memory, not part of the official spec *)
typedef TXIDR_EL0_type = register bits [63:0]
{
  (*63..8 : RES0;*)
  7..0 : DEPTH;
}
register (TXIDR_EL0_type) TXIDR_EL0 (* Transaction ID Register *)



function unit effect pure AArch64_ResetControlRegisters((boolean) cold_reset) =
{
  ()
}
