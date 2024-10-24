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

/*************************************************************************/
/* General system control registers */

register SCR : SCRType /* Secure Configuration Register */

/*************************************************************************/
/* Debug registers */

bitfield DBGOSDLR_type : bits(32) =
{
  /*RES0 : 31..1,*/
  DLK : 0,
}
register DBGOSDLR : DBGOSDLR_type /* Debug OS Double Lock Register */

register DBGPRCR : DBGPRCR_type /* Debug Power Control Register */


/*************************************************************************/
/* Performance Monitors registers */

/*************************************************************************/
/* Generic Timer registers */

/*************************************************************************/
/* Generic Interrupt Controller CPU interface registers */

