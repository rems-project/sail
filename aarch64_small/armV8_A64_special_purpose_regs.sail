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
/*  SPDX-License-Identifier: BSD-2-Clause                                 */
/*========================================================================*/

bitfield CurrentEL_type : bits(32) =
{
  /*RES0 : 31..4,*/
  EL : 3..2,
  /*RES0 : 1..0,*/
}
register CurrentEL : CurrentEL_type /* Current Exception Level */

bitfield DAIF_type : bits(32) =
{
  /*RES0 : 31..10,*/
  D : 9,
  A : 8,
  I : 7,
  F : 6,
  /*RES0 : 5..0,*/
}
register DAIF : DAIF_type /* Interrupt Mask Bits */

bitfield NZCV_type : bits(32) =
{
  N : 31,
  Z : 30,
  C : 29,
  V : 28,
  /*RES0 : 27..0,*/
}
register NZCV : NZCV_type /* Condition Flags */

register SP_EL0 : bits(64) /* Stack Pointer (EL0) */
register SP_EL1 : bits(64) /* Stack Pointer (EL1) */
register SP_EL2 : bits(64) /* Stack Pointer (EL2) */
register SP_EL3 : bits(64) /* Stack Pointer (EL3) */

bitfield SPSel_type : bits(32) =
{
  /*RES0 : 31..1,*/
  SP : 0,
}
register SPSel : SPSel_type /* Stack Pointer Select */

bitfield SPSR_type : bits(32) =
{
  N : 31,
  Z : 30,
  C : 29,
  V : 28,
  /*RES0 : 27..22,*/
  SS : 21,
  IL : 20,
  /*19..10 : RES0*/
   E : 9,
   A : 8,
   I : 7,
   F : 6,
   /*RES0 : 5,*/
   M4 : 4,
   M3_0 : 3..0,
}
register SPSR_EL1 : SPSR_type /* Saved Program Status Register (EL1) */
register SPSR_EL2 : SPSR_type /* Saved Program Status Register (EL2) */
register SPSR_EL3 : SPSR_type /* Saved Program Status Register (EL3) */


register ELR_EL1 : bits(64) /* Exception Link Register (EL1) */
register ELR_EL2 : bits(64) /* Exception Link Register (EL2) */
register ELR_EL3 : bits(64) /* Exception Link Register (EL3) */

