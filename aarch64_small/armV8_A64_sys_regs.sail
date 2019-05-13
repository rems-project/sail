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

/*************************************************************************/
/* General system control registers */


bitfield HCR_type : bits(64) =
{
  /*RES0 : 63..34,*/
  ID : 33,
  CD : 32,
  RW : 31,
  TRVM : 30,
  HCD : 29,
  TDZ : 28,
  TGE : 27,
  TVM : 26,
  TTLB : 25,
  TPU : 24,
  TPC : 23,
  TSW : 22,
  TACR : 21,
  TIDCP : 20,
  TSC : 19,
  TID3 : 18,
  TID2 : 17,
  TID1 : 16,
  TID0 : 15,
  TWE : 14,
  TWI : 13,
  DC : 12,
  BSU : 11..10,
  FB : 9,
  VSE : 8,
  VI : 7,
  VF : 6,
  AMO : 5,
  IMO : 4,
  FMO : 3,
  PTW : 2,
  SWIO : 1,
  VM : 0,
}
register HCR_EL2 : HCR_type /* Hypervisor Configuration Register */


bitfield ID_AA64MMFR0_type : bits(64) =
{
  /*RES0 : 63..32,*/
  TGran4 : 31..28,
  TGran64 : 27..24,
  TGran16 : 23..20,
  BigEndEL0 : 19..16,
  SNSMem : 15..12,
  BigEnd : 11..8,
   ASIDBits : 7..4,
   PARange : 3..0,
}
register ID_AA64MMFR0_EL1 : ID_AA64MMFR0_type /* AArch64 Memory Model Feature Register 0 */

register RVBAR_EL1 : bits(64) /* Reset Vector Base Address Register (if EL2 and EL3 not implemented) */
register RVBAR_EL2 : bits(64) /* Reset Vector Base Address Register (if EL3 not implemented) */
register RVBAR_EL3 : bits(64) /* Reset Vector Base Address Register (if EL3 implemented) */

bitfield SCRType : bits(32) =
{
  /*RES0 : 31..14,*/
  TWE : 13,
  TWI : 12,
  ST : 11,
  RW : 10,
  SIF : 9,
  HCE : 8,
  SMD : 7,
  /*RES0 : 6,*/
  /*RES1 : 5..4,*/
  EA : 3,
  FIQ : 2,
  IRQ : 1,
  NS : 0,
}
register SCR_EL3 : SCRType /* Secure Configuration Register */

bitfield SCTLR_EL1_type : bits(32) =
{
  /*RES0 : 31..30,*/
  /*RES1 : 29..28,*/
  /*RES0 : 27,*/
  UCI : 26,
  EE : 25,
  E0E : 24,
  /*RES1 : 23..22,*/
  /*RES0 : 21,*/
  /*RES1 : 20,*/
  WXN : 19,
  nTWE : 18,
  /*RES0 : 17,*/
  nTWI : 16,
  UCT : 15,
  DZE : 14,
  /*RES0 : 13,*/
  I : 12,
  /*RES1 : 11,*/
  /*RES0 : 10,*/
  UMA : 9,
  SED : 8,
  ITD : 7,
  /*RES0 : 6,*/
  CP15BEN : 5,
  SA0 : 4,
  SA : 3,
  C : 2,
  A : 1,
  M : 0,
}
register SCTLR_EL1 : SCTLR_EL1_type /* System Control Register (EL1) */

bitfield SCTLR_type : bits(32) =
{
  /*RES0 : 31..30,*/
  /*RES1 : 29..28,*/
  /*RES0 : 27..26,*/
  EE : 25,
  /*RES0 : 24,*/
  /*RES1 : 23..22,*/
  /*RES0 : 21..20,*/
  WXN : 19,
  /*RES1 : 18,*/
  /*RES0 : 17,*/
  /*RES1 : 16,*/
  /*RES0 : 15..13,*/
  I : 12,
  /*RES1 : 11,*/
  /*RES0 : 10..6,*/
  /*RES1 : 5..4,*/
  SA : 3,
  C : 2,
  A : 1,
  M : 0,
}
register SCTLR_EL2 : SCTLR_type /* System Control Register (EL2) */
register SCTLR_EL3 : SCTLR_type /* System Control Register (EL3) */



/* CP: added coercion from SCTLR_EL1_type to SCTLR_type for the SCTLR function */
val cast "SCTLR_EL1_type_to_SCTLR_type" : SCTLR_EL1_type -> SCTLR_type

bitfield TCR_EL1_type : bits(64) =
{
  /*RES0 : 63..39,*/
  TBI1 : 38,
  TBI0 : 37,
  AS : 36,
  /*RES0 : 35,*/
  IPS : 34..32,
  TG1 : 31..30,
  SH1 : 29..28,
  ORGN1 : 27..26,
  IRGN1 : 25..24,
  EPD1 : 23,
  A1 : 22,
  T1SZ : 21..16,
  TG0 : 15..14,
  SH0 : 13..12,
  ORGN0 : 11..10,
  IRGN0 : 9..8,
  EPD0 : 7,
  /*RES0 : 6,*/
  T0SZ : 5..0,
}
register TCR_EL1 : TCR_EL1_type /* Translation Control Register (EL1) */

bitfield TCR_type : bits(32) =
{
  /*RES1 : 31,*/
  /*RES0 : 30..24,*/
  /*RES1 : 23,*/
  /*RES0 : 22..21,*/
  TBI : 20,
  /*RES0 : 19,*/
  PS : 18..16,
  TG0 : 15..14,
  SH0 : 13..12,
  ORGN0 : 11..10,
  IRGN0 : 9..8,
  /*RES0 : 7..6,*/
  T0SZ : 5..0,
}
register TCR_EL2 : TCR_type /* Translation Control Register (EL2) */
register TCR_EL3 : TCR_type /* Translation Control Register (EL3) */

register TPIDR_EL0 : bits(64) /* EL0 Read/Write Software Thread ID Register */
register TPIDR_EL1 : bits(64) /* EL1 Read/Write Software Thread ID Register */
register TPIDR_EL2 : bits(64) /* EL2 Read/Write Software Thread ID Register */
register TPIDR_EL3 : bits(64) /* EL3 Read/Write Software Thread ID Register */

/*************************************************************************/
/* Debug registers */

bitfield DBGPRCR_type : bits(32) =
{
  /*RES0 : 31..1,*/
  CORENPDRQ : 0,
}
register DBGPRCR_EL1 : DBGPRCR_type /* Debug Power Control Register */

bitfield OSDLR_type : bits(32) =
{
  /*RES0 : 31..1,*/
  DLK : 0,
}
register OSDLR_EL1 : OSDLR_type /* OS Double Lock Register */

/*************************************************************************/
/* Performance Monitors registers */

/*************************************************************************/
/* Generic Timer registers */

/*************************************************************************/
/* Generic Interrupt Controller CPU interface registers */

/*************************************************************************/
/* External Debug Register */

bitfield EDSCR_type : bits(32) =
{
  /*RES0 : 31,*/
  RXfull : 30,
  TXfull : 29,
  ITO : 28,
  RXO : 27,
  TXU : 26,
  PipeAdv : 25,
  ITE : 24,
  INTdis : 23..22,
  TDA : 21,
  MA : 20,
  /*RES0 : 19,*/
  NS : 18,
  /*RES0 : 17,*/
  SDD : 16,
  /*RES0 : 15,*/
  HDE : 14,
  RW : 13..10,
  EL : 9..8,
  A : 7,
  ERR : 6,
  STATUS : 5..0,
}
register EDSCR : EDSCR_type /* External Debug Status and Control Register */

/* transactional memory, not part of the official spec */
bitfield TXIDR_EL0_type : bits(64) =
{
  /*RES0 : 63..8,*/
  DEPTH : 7..0,
}
register TXIDR_EL0 : TXIDR_EL0_type /* Transaction ID Register */


val AArch64_ResetControlRegisters : boolean -> unit effect pure
function AArch64_ResetControlRegisters(cold_reset) = ()

