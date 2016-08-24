(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2016 Shaked Flur                                   *)
(*  Copyright (c) 2015-2016 Kathyrn Gray                                  *)
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

register (bit[32]) ACTLR_EL1 (* Auxiliary Control Register (EL1) *) (* UNUSED *)
register (bit[32]) ACTLR_EL2 (* Auxiliary Control Register (EL2) *) (* UNUSED *)
register (bit[32]) ACTLR_EL3 (* Auxiliary Control Register (EL3) *) (* UNUSED *)
register (bit[32]) AFSR0_EL1 (* Auxiliary Fault Status Register 0 (EL1) *) (* UNUSED *)
register (bit[32]) AFSR0_EL2 (* Auxiliary Fault Status Register 0 (EL2) *) (* UNUSED *)
register (bit[32]) AFSR0_EL3 (* Auxiliary Fault Status Register 0 (EL3) *) (* UNUSED *)
register (bit[32]) AFSR1_EL1 (* Auxiliary Fault Status Register 1 (EL1) *) (* UNUSED *)
register (bit[32]) AFSR1_EL2 (* Auxiliary Fault Status Register 1 (EL2) *) (* UNUSED *)
register (bit[32]) AFSR1_EL3 (* Auxiliary Fault Status Register 1 (EL3) *) (* UNUSED *)
register (bit[32]) AIDR_EL1  (* Auxiliary ID Register *) (* UNUSED *)
register (bit[64]) AMAIR_EL1 (* Auxiliary Memory Attribute Indirection Register (EL1) *) (* UNUSED *)
register (bit[64]) AMAIR_EL2 (* Auxiliary Memory Attribute Indirection Register (EL2) *) (* UNUSED *)
register (bit[64]) AMAIR_EL3 (* Auxiliary Memory Attribute Indirection Register (EL3) *) (* UNUSED *)

typedef CCSIDR_type = register bits [31:0]
{
  31     : WT;
  30     : WB;
  29     : RA;
  28     : WA;
  27..13 : NumSets;
  12..3  : Associativity;
  2..0   : LineSize;
}
register (CCSIDR_type) CCSIDR_EL1 (* Current Cache Size ID Register *) (* UNUSED *)

typedef CLIDR_type = register bits [63:0]
{
  (*63..33 : RES0*)
  32..30 : ICB;
  29..27 : LoUU;
  26..24 : LoC;
  23..21 : LoUIS;
  20..18 : Ctype7;
  17..15 : Ctype6;
  14..12 : Ctype5;
  11..9  : Ctype4;
  8..6   : Ctype3;
  5..3   : Ctype2;
  2..0   : Ctype1;
}
register (CLIDR_type) CLIDR_EL1 (* Cache Level ID Register *) (* UNUSED *)

typedef CONTEXTIDR_type = register bits [31:0] { 31..0 : PROCID }
register (CONTEXTIDR_type) CONTEXTIDR_EL1 (* Context ID Register *) (* UNUSED *)

typedef CPACR_type = register bits [31:0]
{
  (*31..29 : RES0;*)
  28 : TTA;
  (*27..22 : RES0;*)
  21..20 : FPEN;
  (*19..0 : RES0;*)
}
register (CPACR_type) CPACR_EL1 (* Architectural Feature Access Control Register *) (* UNUSED *)

typedef CPTR_type = register bits [31:0]
{
  (* in EL3 all the RES are RES0 *)
  31 : TCPAC;
  (*30..21 : RES0;*)
  20 : TTA;
  (*19..14 : RES0;*)
  (*13..12 : RES1;*)
  (*11 : RES0;*)
  10 : TFP;
  (*9..0 : RES1;*)
}
register (CPTR_type) CPTR_EL2 (* Architectural Feature Trap Register (EL2) *) (* UNUSED *)
register (CPTR_type) CPTR_EL3 (* Architectural Feature Trap Register (EL3) *) (* UNUSED *)

typedef CSSELR_type = register bits [31:0]
{
  (*31..4 : RES0;*)
  3..1 : Level;
  0    : InD;
}
register (CSSELR_type) CSSELR_EL1 (* Cache Size Selection Register *) (* UNUSED *)

typedef CTR_type = register bits [31:0]
{
  (*31 : RES1;*)
  (*30..28 : RES0;*)
  27..24 : CWG;
  23..20 : ERG;
  19..16 : DminLine;
  15..14 : L1Ip;
  (*13..4 : RES0;*)
  3..0 : IminLine;
}
register (CTR_type) CTR_EL0 (* Cache Type Register *) (* UNUSED *)

typedef DACR32_type = register bits [31:0]
{
  31..30 : D15;
  29..28 : D14;
  27..26 : D13;
  25..24 : D12;
  23..22 : D11;
  21..20 : D10;
  29..18 : D9;
  17..16 : D8;
  15..14 : D7;
  13..12 : D6;
  11..10 : D5;
  9..8   : D4;
  7..6   : D3;
  5..4   : D2;
  3..2   : D1;
  1..0   : D0;
}
register (DACR32_type) DACR32_EL2 (* Domain Access Control Register *) (* UNUSED *)

typedef DCZID_type = register bits [31:0]
{
  (*31..5 : RES0;*)
  4    : DZP;
  3..0 : BS;
}
register (DCZID_type) DCZID_EL0 (* Data Cache Zero ID register *) (* UNUSED *)

typedef ESR_type = register bits [31:0]
{
  31..26 : EC;
  25     : IL;
  24..0  : ISS;
}
register (ESR_type) ESR_EL1 (* Exception Syndrome Register (EL1) *) (* UNUSED *)
register (ESR_type) ESR_EL2 (* Exception Syndrome Register (EL2) *) (* UNUSED *)
register (ESR_type) ESR_EL3 (* Exception Syndrome Register (EL3) *) (* UNUSED *)

register (bit[64]) FAR_EL1 (* Fault Address Register (EL1) *) (* UNUSED *)
register (bit[64]) FAR_EL2 (* Fault Address Register (EL2) *) (* UNUSED *)
register (bit[64]) FAR_EL3 (* Fault Address Register (EL3) *) (* UNUSED *)

typedef FPEXC32_type = register bits [31:0]
{
  31 : EX;
  30 : EN;
  29 : DEX;
  28 : FP2V;
  27 : VV;
  26 : TFV;
  (*25..21 : RES0;*)
  (*20..11 : IMPLEMENTATION DEFINED*)
  10..8 : VECITR;
  7 : IDF;
  (*6..5 : IMPLEMENTATION DEFINED*)
  4 : IXF;
  3 : UFF;
  2 : OFF;
  1 : DZF;
  0 : IOF;
}
register (FPEXC32_type) FPEXC32_EL2 (* Floating-point Exception Control register *) (* UNUSED *)
register (bit[32]) HACR_EL2 (* Hypervisor Auxiliary Control Register *) (* UNUSED *)

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

typedef HPFAR_type = register bits [63:0]
{
  (*63..40 : RES0;*)
  39..4 : FIPA; (* bits [47:12] of FIPA *)
  (*3..0 : RES0;*)
}
register (HPFAR_type) HPFAR_EL2 (* Hypervisor IPA Fault Address Register *) (* UNUSED *)

typedef HSTR_type = register bits [31:0]
{
  (*31..16 : RES0;*)
  15 : T15;
  14 : T14;
  13 : T13;
  12 : T12;
  11 : T11;
  10 : T10;
  9  : T9;
  8  : T8;
  7  : T7;
  6  : T6;
  5  : T5;
  4  : T4;
  3  : T3;
  2  : T2;
  1  : T1;
  0  : T0;
}
register (HSTR_type) HSTR_EL2 (* Hypervisor System Trap Register *) (* UNUSED *)

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


function unit effect pure AArch64_ResetControlRegisters((boolean) cold_reset) =
{
  ()
}

