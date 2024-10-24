/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*    Louis-Emile Ploix                                                     */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

%{

[@@@coverage exclude_file]

open Libsail.Jib

%}

%token Colon Lsquare Rsquare Underscore
%token Bit Int Logic String
%token SailBits SailInt SailList
%token Eof

%token <int> Nat
%token <int> HashNat

%start sv_type
%type <int option * ctyp> sv_type

%%

sv_type:
  | p = packed_type; u = unpacked_type_opt; Eof
    { let (n, f) = u in (n, f p) }

packed_type:
  | Bit
    { CT_bool }
  | SailInt
    { CT_lint }
  | SailBits
    { CT_lbits }
  | Int
    { CT_fint 32 }
  | String
    { CT_string }
  | Logic; Lsquare; d = dimensions; Rsquare
    { CT_fbits d }

dimensions:
  | hi = Nat; Colon; lo = Nat
    { (hi + 1) - lo }
  | len = Nat
    { len }

unpacked_type_opt:
  |
    { (None, fun ty -> ty) }
  | n = HashNat
    { (Some n, fun ty -> ty) }
  | Underscore; u = unpacked_type
    { (None, u) }
  | n = HashNat; u = unpacked_type
    { (Some n, u) }

unpacked_type:
  | SailList
    { fun ty -> CT_list ty }
  | Lsquare; d = dimensions; Rsquare
    { fun ty -> CT_fvector (d, ty) }
