/**************************************************************************/
/*     Sail                                                               */
/*                                                                        */
/*  Copyright (c) 2013-2017                                               */
/*    Kathyrn Gray                                                        */
/*    Shaked Flur                                                         */
/*    Stephen Kell                                                        */
/*    Gabriel Kerneis                                                     */
/*    Robert Norton-Wright                                                */
/*    Christopher Pulte                                                   */
/*    Peter Sewell                                                        */
/*    Alasdair Armstrong                                                  */
/*    Brian Campbell                                                      */
/*    Thomas Bauereiss                                                    */
/*    Anthony Fox                                                         */
/*    Jon French                                                          */
/*    Dominic Mulligan                                                    */
/*    Stephen Kell                                                        */
/*    Mark Wassell                                                        */
/*                                                                        */
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
/**************************************************************************/

%{

let r = fun x -> x (* Ulib.Text.of_latin1 *)

module Big_int = Nat_big_num
open Parse_ast

let loc n m = Range (n, m)

let default_opt x = function
  | None -> x
  | Some y -> y

let assoc_opt key (assocs, default) =
  try Some (List.assoc key assocs) with
  | Not_found -> default

let cons_fst h (t,x) = (h::t,x)

let string_of_id = function
  | Id_aux (Id str, _) -> str
  | Id_aux (DeIid str, _) -> str

let prepend_id str1 = function
  | Id_aux (Id str2, loc) -> Id_aux (Id (str1 ^ str2), loc)
  | _ -> assert false

let mk_id i n m = Id_aux (i, loc n m)
let mk_kid str n m = Kid_aux (Var str, loc n m)

let mk_kopt k n m = KOpt_aux (k, loc n m)

let id_of_kid = function
  | Kid_aux (Var v, l) -> Id_aux (Id (String.sub v 1 (String.length v - 1)), l)

let deinfix = function
  | (Id_aux (Id v, l)) -> Id_aux (DeIid v, l)
  | (Id_aux (DeIid v, l)) -> Id_aux (Id v, l)

let mk_effect e n m = BE_aux (e, loc n m)
let mk_typ t n m = ATyp_aux (t, loc n m)
let mk_pat p n m = P_aux (p, loc n m)
let mk_pexp p n m = Pat_aux (p, loc n m)
let mk_exp e n m = E_aux (e, loc n m)
let mk_lit l n m = L_aux (l, loc n m)
let mk_lit_exp l n m = mk_exp (E_lit (mk_lit l n m)) n m
let mk_typschm tq t n m = TypSchm_aux (TypSchm_ts (tq, t), loc n m)

let mk_typschm_opt ts n m = TypSchm_opt_aux (
                                  TypSchm_opt_some (
                                      ts
                                    ),
                                  loc n m
                                )

let mk_typschm_opt_none = TypSchm_opt_aux (TypSchm_opt_none, Unknown)

let mk_sd s n m = SD_aux (s, loc n m)
let mk_sd_doc s str n m = SD_aux (s, Documented (str, loc n m))
let mk_ir r n m = BF_aux (r, loc n m)

let mk_funcl f n m = FCL_aux (f, loc n m)
let mk_fun fn n m = FD_aux (fn, loc n m)
let mk_td t n m = TD_aux (t, loc n m)
let mk_vs v n m = VS_aux (v, loc n m)
let mk_reg_dec d n m = DEC_aux (d, loc n m)
let mk_default d n m = DT_aux (d, loc n m)

let mk_mpexp mpexp n m = MPat_aux (mpexp, loc n m)
let mk_mpat mpat n m = MP_aux (mpat, loc n m)
let mk_bidir_mapcl mpexp1 mpexp2 n m = MCL_aux (MCL_bidir (mpexp1, mpexp2), loc n m)
let mk_forwards_mapcl mpexp exp n m = MCL_aux (MCL_forwards (mpexp, exp), loc n m)
let mk_backwards_mapcl mpexp exp n m = MCL_aux (MCL_backwards (mpexp, exp), loc n m)
let mk_map id tannot mapcls n m = MD_aux (MD_mapping (id, tannot, mapcls), loc n m)

let doc_vs doc (VS_aux (v, l)) = VS_aux (v, Documented (doc, l))

let qi_id_of_kopt (KOpt_aux (kopt_aux, l) as kopt) = QI_aux (QI_id kopt, l)

let mk_recr r n m = (Rec_aux(r, loc n m))

let mk_recn = (Rec_aux((Rec_nonrec), Unknown))
let mk_typqn = (TypQ_aux(TypQ_no_forall,Unknown))
let mk_tannotn = Typ_annot_opt_aux(Typ_annot_opt_none,Unknown)
let mk_tannot typq typ n m = Typ_annot_opt_aux(Typ_annot_opt_some (typq, typ), loc n m)
let mk_eannotn = Effect_opt_aux(Effect_opt_pure,Unknown)
let mk_namesectn = Name_sect_aux(Name_sect_none,Unknown)

let mk_typq kopts nc n m = TypQ_aux (TypQ_tq (List.map qi_id_of_kopt kopts @ nc), loc n m)

type lchain =
  LC_lt
| LC_lteq
| LC_nexp of atyp

let tyop op t1 t2 s e = mk_typ (ATyp_app (Id_aux (DeIid op, loc s e), [t1; t2])) s e

let rec desugar_lchain chain s e =
  match chain with
  | [LC_nexp n1; LC_lteq; LC_nexp n2] -> tyop "<=" n1 n2 s e
  | [LC_nexp n1; LC_lt; LC_nexp n2] -> tyop "<" n1 n2 s e
  | (LC_nexp n1 :: LC_lteq :: LC_nexp n2 :: chain) ->
     let nc1 = tyop "<=" n1 n2 s e in
     tyop "&" nc1 (desugar_lchain (LC_nexp n2 :: chain) s e) s e
  | (LC_nexp n1 :: LC_lt :: LC_nexp n2 :: chain) ->
     let nc1 = tyop "<" n1 n2 s e in
     tyop "&" nc1 (desugar_lchain (LC_nexp n2 :: chain) s e) s e
  | _ -> assert false

type rchain =
  RC_gt
| RC_gteq
| RC_nexp of atyp

let rec desugar_rchain chain s e =
  match chain with
  | [RC_nexp n1; RC_gteq; RC_nexp n2] -> tyop ">=" n1 n2 s e
  | [RC_nexp n1; RC_gt; RC_nexp n2] -> tyop ">" n1 n2 s e
  | (RC_nexp n1 :: RC_gteq :: RC_nexp n2 :: chain) ->
     let nc1 = tyop ">=" n1 n2 s e in
     tyop "&" nc1 (desugar_rchain (RC_nexp n2 :: chain) s e) s e
  | (RC_nexp n1 :: RC_gt :: RC_nexp n2 :: chain) ->
     let nc1 = tyop ">" n1 n2 s e in
     tyop "&" nc1 (desugar_rchain (RC_nexp n2 :: chain) s e) s e
  | _ -> assert false

%}

/*Terminals with no content*/

%token And As Assert Bitzero Bitone By Match Clause Dec Default Effect End Op Where
%token Enum Else False Forall Foreach Overload Function_ Mapping If_ In Inc Let_ Int Order Bool Cast
%token Pure Register Return Scattered Sizeof Struct Then True TwoCaret TYPE Typedef
%token Undefined Union Newtype With Val Constant Constraint Throw Try Catch Exit Bitfield
%token Barr Depend Rreg Wreg Rmem Rmemt Wmem Wmv Wmvt Eamem Exmem Undef Unspec Nondet Escape
%token Repeat Until While Do Mutual Var Ref Configuration TerminationMeasure

%nonassoc Then
%nonassoc Else

%token Bar Comma Dot Eof Minus Semi Under DotDot
%token Lcurly Rcurly Lparen Rparen Lsquare Rsquare LcurlyBar RcurlyBar LsquareBar RsquareBar
%token MinusGt Bidir LtMinus

/*Terminals with content*/

%token <string> Id TyVar
%token <Nat_big_num.num> Num
%token <string> String Bin Hex Real

%token <string> Amp At Caret Eq Gt Lt Plus Star EqGt Unit
%token <string> Colon ColonColon TildeTilde ExclEq
%token <string> EqEq
%token <string> GtEq
%token <string> LtEq

%token <string> Doc

%token <string> Op0 Op1 Op2 Op3 Op4 Op5 Op6 Op7 Op8 Op9
%token <string> Op0l Op1l Op2l Op3l Op4l Op5l Op6l Op7l Op8l Op9l
%token <string> Op0r Op1r Op2r Op3r Op4r Op5r Op6r Op7r Op8r Op9r

%token <string * string> Pragma

%token <Parse_ast.fixity_token> Fixity

%start file
%start typschm_eof
%start typ_eof
%start exp_eof
%start def_eof
%type <Parse_ast.typschm> typschm_eof
%type <Parse_ast.atyp> typ_eof
%type <Parse_ast.exp> exp_eof
%type <Parse_ast.def> def_eof
%type <Parse_ast.defs> file

%%

id:
  | Id { mk_id (Id $1) $startpos $endpos }

  | Op Op0 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op1 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op2 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op3 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op4 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op5 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op6 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op7 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op8 { mk_id (DeIid $2) $startpos $endpos }
  | Op Op9 { mk_id (DeIid $2) $startpos $endpos }

  | Op Op0l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op1l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op2l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op3l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op4l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op5l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op6l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op7l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op8l { mk_id (DeIid $2) $startpos $endpos }
  | Op Op9l { mk_id (DeIid $2) $startpos $endpos }

  | Op Op0r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op1r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op2r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op3r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op4r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op5r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op6r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op7r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op8r { mk_id (DeIid $2) $startpos $endpos }
  | Op Op9r { mk_id (DeIid $2) $startpos $endpos }

  | Op Plus { mk_id (DeIid "+") $startpos $endpos }
  | Op Minus { mk_id (DeIid "-") $startpos $endpos }
  | Op Star { mk_id (DeIid "*") $startpos $endpos }
  | Op EqEq { mk_id (DeIid "==") $startpos $endpos }
  | Op ExclEq { mk_id (DeIid "!=") $startpos $endpos }
  | Op Lt { mk_id (DeIid "<") $startpos $endpos }
  | Op Gt { mk_id (DeIid ">") $startpos $endpos }
  | Op LtEq { mk_id (DeIid "<=") $startpos $endpos }
  | Op GtEq { mk_id (DeIid ">=") $startpos $endpos }
  | Op Amp { mk_id (DeIid "&") $startpos $endpos }
  | Op Bar { mk_id (DeIid "|") $startpos $endpos }
  | Op Caret { mk_id (DeIid "^") $startpos $endpos }

op0: Op0 { mk_id (Id $1) $startpos $endpos }
op1: Op1 { mk_id (Id $1) $startpos $endpos }
op2: Op2 { mk_id (Id $1) $startpos $endpos }
op3: Op3 { mk_id (Id $1) $startpos $endpos }
op4: Op4 { mk_id (Id $1) $startpos $endpos }
op5: Op5 { mk_id (Id $1) $startpos $endpos }
op6: Op6 { mk_id (Id $1) $startpos $endpos }
op7: Op7 { mk_id (Id $1) $startpos $endpos }
op8: Op8 { mk_id (Id $1) $startpos $endpos }
op9: Op9 { mk_id (Id $1) $startpos $endpos }

op0l: Op0l { mk_id (Id $1) $startpos $endpos }
op1l: Op1l { mk_id (Id $1) $startpos $endpos }
op2l: Op2l { mk_id (Id $1) $startpos $endpos }
op3l: Op3l { mk_id (Id $1) $startpos $endpos }
op4l: Op4l { mk_id (Id $1) $startpos $endpos }
op5l: Op5l { mk_id (Id $1) $startpos $endpos }
op6l: Op6l { mk_id (Id $1) $startpos $endpos }
op7l: Op7l { mk_id (Id $1) $startpos $endpos }
op8l: Op8l { mk_id (Id $1) $startpos $endpos }
op9l: Op9l { mk_id (Id $1) $startpos $endpos }

op0r: Op0r { mk_id (Id $1) $startpos $endpos }
op1r: Op1r { mk_id (Id $1) $startpos $endpos }
op2r: Op2r { mk_id (Id $1) $startpos $endpos }
op3r: Op3r { mk_id (Id $1) $startpos $endpos }
op4r: Op4r { mk_id (Id $1) $startpos $endpos }
op5r: Op5r { mk_id (Id $1) $startpos $endpos }
op6r: Op6r { mk_id (Id $1) $startpos $endpos }
op7r: Op7r { mk_id (Id $1) $startpos $endpos }
op8r: Op8r { mk_id (Id $1) $startpos $endpos }
op9r: Op9r { mk_id (Id $1) $startpos $endpos }

id_list:
  | id
    { [$1] }
  | id Comma id_list
    { $1 :: $3 }

kid:
  | TyVar
    { mk_kid $1 $startpos $endpos }

num_list:
  | Num
    { [$1] }
  | Num Comma num_list
    { $1 :: $3 }

lchain:
  | typ5 LtEq typ5
    { [LC_nexp $1; LC_lteq; LC_nexp $3] }
  | typ5 Lt typ5
    { [LC_nexp $1; LC_lt; LC_nexp $3] }
  | typ5 LtEq lchain
    { LC_nexp $1 :: LC_lteq :: $3 }
  | typ5 Lt lchain
    { LC_nexp $1 :: LC_lt :: $3 }

rchain:
  | typ5 GtEq typ5
    { [RC_nexp $1; RC_gteq; RC_nexp $3] }
  | typ5 Gt typ5
    { [RC_nexp $1; RC_gt; RC_nexp $3] }
  | typ5 GtEq rchain
    { RC_nexp $1 :: RC_gteq :: $3 }
  | typ5 Gt rchain
    { RC_nexp $1 :: RC_gt :: $3 }

tyarg:
  | Lparen typ_list Rparen
    { [], $2 }

typ_eof:
  | typ Eof
    { $1 }

typ:
  | typ0
    { $1 }

/* The following implements all nine levels of user-defined precedence for
operators in types, with both left, right and non-associative operators */

typ0:
  | typ1 op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ0l op0l typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 op0r typ0r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }
typ0l:
  | typ1 op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ0l op0l typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }
typ0r:
  | typ1 op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 op0r typ0r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }

typ1:
  | typ2 op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1l op1l typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 op1r typ1r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }
typ1l:
  | typ2 op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1l op1l typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }
typ1r:
  | typ2 op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 op1r typ1r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }

typ2:
  | typ3 op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2l op2l typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 op2r typ2r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 Bar typ2r { mk_typ (ATyp_app (deinfix (mk_id (Id "|") $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ3 { $1 }
typ2l:
  | typ3 op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2l op2l typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 { $1 }
typ2r:
  | typ3 op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 op2r typ2r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 Bar typ2r { mk_typ (ATyp_app (deinfix (mk_id (Id "|") $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ3 { $1 }

typ3:
  | typ4 op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3l op3l typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 op3r typ3r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 Amp typ3r { mk_typ (ATyp_app (deinfix (mk_id (Id "&") $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ4 { $1 }
typ3l:
  | typ4 op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3l op3l typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 { $1 }
typ3r:
  | typ4 op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 op3r typ3r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 Amp typ3r { mk_typ (ATyp_app (deinfix (mk_id (Id "&") $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ4 { $1 }

typ4:
  | typ5 op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4l op4l typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 op4r typ4r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | lchain { desugar_lchain $1 $startpos $endpos }
  | rchain { desugar_rchain $1 $startpos $endpos }
  | typ5 EqEq typ5 { mk_typ (ATyp_app (deinfix (mk_id (Id $2) $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ5 ExclEq typ5 { mk_typ (ATyp_app (deinfix (mk_id (Id $2) $startpos($2) $endpos($2)), [$1; $3])) $startpos $endpos }
  | typ5 { $1 }
typ4l:
  | typ5 op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4l op4l typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 { $1 }
typ4r:
  | typ5 op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 op4r typ4r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 { $1 }

typ5:
  | typ6 op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5l op5l typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 op5r typ5r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }
typ5l:
  | typ6 op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5l op5l typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }
typ5r:
  | typ6 op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 op5r typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }

typ6:
  | typ7 op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l op6l typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 op6r typ6r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Plus typ7 { mk_typ (ATyp_sum ($1, $3)) $startpos $endpos }
  | typ6l Minus typ7 { mk_typ (ATyp_minus ($1, $3)) $startpos $endpos }
  | typ7 { $1 }
typ6l:
  | typ7 op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l op6l typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Plus typ7 { mk_typ (ATyp_sum ($1, $3)) $startpos $endpos }
  | typ6l Minus typ7 { mk_typ (ATyp_minus ($1, $3)) $startpos $endpos }
  | typ7 { $1 }
typ6r:
  | typ7 op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 op6r typ6r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 { $1 }

typ7:
  | typ8 op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l op7l typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 op7r typ7r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Star typ8 { mk_typ (ATyp_times ($1, $3)) $startpos $endpos }
  | typ8 { $1 }
typ7l:
  | typ8 op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l op7l typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Star typ8 { mk_typ (ATyp_times ($1, $3)) $startpos $endpos }
  | typ8 { $1 }
typ7r:
  | typ8 op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 op7r typ7r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 { $1 }

typ8:
  | typ9 op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8l op8l typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9 op8r typ8r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }
typ8l:
  | typ9 op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8l op8l typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }
typ8r:
  | typ9 op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9 op8r typ8r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }

typ9:
  | kid In Lcurly num_list Rcurly
    { mk_typ (ATyp_nset ($1, $4)) $startpos $endpos }
  | atomic_typ op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9l op9l atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ op9r typ9r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }
typ9l:
  | atomic_typ op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9l op9l atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }
typ9r:
  | atomic_typ op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ op9r typ9r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }

atomic_typ:
  | id
    { mk_typ (ATyp_id $1) $startpos $endpos }
  | Under
    { mk_typ ATyp_wild $startpos $endpos }
  | kid
    { mk_typ (ATyp_var $1) $startpos $endpos }
  | lit
    { mk_typ (ATyp_lit $1) $startpos $endpos }
  | Dec
    { mk_typ ATyp_dec $startpos $endpos }
  | Inc
    { mk_typ ATyp_inc $startpos $endpos }
  | id tyarg
    { mk_typ (ATyp_app ($1, snd $2 @ fst $2)) $startpos $endpos }
  | Register Lparen typ Rparen
    { let register_id = mk_id (Id "register") $startpos($1) $endpos($1) in
      mk_typ (ATyp_app (register_id, [$3])) $startpos $endpos }
  | Lparen typ Rparen
    { $2 }
  | Lparen typ Comma typ_list Rparen
    { mk_typ (ATyp_tup ($2 :: $4)) $startpos $endpos }
  | LcurlyBar num_list RcurlyBar
    { let v = mk_kid "n" $startpos $endpos in
      let atom_id = mk_id (Id "atom") $startpos $endpos in
      let atom_of_v = mk_typ (ATyp_app (atom_id, [mk_typ (ATyp_var v) $startpos $endpos])) $startpos $endpos in
      mk_typ (ATyp_exist ([mk_kopt (KOpt_none v) $startpos $endpos], ATyp_aux (ATyp_nset (v, $2), loc $startpos($2) $endpos($2)), atom_of_v)) $startpos $endpos }
  | Lcurly kopt_list Dot typ Rcurly
    { mk_typ (ATyp_exist ($2, ATyp_aux (ATyp_lit (L_aux (L_true, loc $startpos $endpos)), loc $startpos $endpos), $4)) $startpos $endpos }
  | Lcurly kopt_list Comma typ Dot typ Rcurly
    { mk_typ (ATyp_exist ($2, $4, $6)) $startpos $endpos }
  | Lcurly id Colon typ Dot typ Rcurly
    { mk_typ (ATyp_base ($2, $4, $6)) $startpos $endpos }

typ_list:
  | typ
    { [$1] }
  | typ Comma typ_list
    { $1 :: $3 }

kind:
  | Int
    { K_aux (K_int, loc $startpos $endpos) }
  | TYPE
    { K_aux (K_type, loc $startpos $endpos) }
  | Order
    { K_aux (K_order, loc $startpos $endpos) }
  | Bool
    { K_aux (K_bool, loc $startpos $endpos) }

kopt:
  | Lparen kid Colon kind Rparen
    { KOpt_aux (KOpt_kind ($4, $2), loc $startpos $endpos) }
  | kid
    { KOpt_aux (KOpt_none $1, loc $startpos $endpos) }

kopt_list:
  | kopt
    { [$1] }
  | kopt kopt_list
    { $1 :: $2 }

typquant:
  | kopt_list Comma typ
    { let qi_nc = QI_aux (QI_const $3, loc $startpos($3) $endpos($3)) in
      TypQ_aux (TypQ_tq (List.map qi_id_of_kopt $1 @ [qi_nc]), loc $startpos $endpos) }
  | kopt_list
    { TypQ_aux (TypQ_tq (List.map qi_id_of_kopt $1), loc $startpos $endpos) }

effect:
  | Barr
    { mk_effect BE_barr $startpos $endpos }
  | Depend
    { mk_effect BE_depend $startpos $endpos }
  | Rreg
    { mk_effect BE_rreg $startpos $endpos }
  | Wreg
    { mk_effect BE_wreg $startpos $endpos }
  | Rmem
    { mk_effect BE_rmem $startpos $endpos }
  | Rmemt
    { mk_effect BE_rmemt $startpos $endpos }
  | Wmem
    { mk_effect BE_wmem $startpos $endpos }
  | Wmv
    { mk_effect BE_wmv $startpos $endpos }
  | Wmvt
    { mk_effect BE_wmvt $startpos $endpos }
  | Eamem
    { mk_effect BE_eamem $startpos $endpos }
  | Exmem
    { mk_effect BE_exmem $startpos $endpos }
  | Undef
    { mk_effect BE_undef $startpos $endpos }
  | Unspec
    { mk_effect BE_unspec $startpos $endpos }
  | Nondet
    { mk_effect BE_nondet $startpos $endpos }
  | Escape
    { mk_effect BE_escape $startpos $endpos }
  | Configuration
    { mk_effect BE_config $startpos $endpos }

effect_list:
  | effect
    { [$1] }
  | effect Comma effect_list
    { $1::$3 }

effect_set:
  | Lcurly effect_list Rcurly
    { mk_typ (ATyp_set $2) $startpos $endpos }
  | Pure
    { mk_typ (ATyp_set []) $startpos $endpos }

typschm:
  | typ MinusGt typ
    { (fun s e -> mk_typschm mk_typqn (mk_typ (ATyp_fn ($1, $3, mk_typ (ATyp_set []) s e)) s e) s e) $startpos $endpos }
  | Forall typquant Dot typ MinusGt typ
    { (fun s e -> mk_typschm $2 (mk_typ (ATyp_fn ($4, $6, mk_typ (ATyp_set []) s e)) s e) s e) $startpos $endpos }
  | typ MinusGt typ Effect effect_set
    { (fun s e -> mk_typschm mk_typqn (mk_typ (ATyp_fn ($1, $3, $5)) s e) s e) $startpos $endpos }
  | Forall typquant Dot typ MinusGt typ Effect effect_set
    { (fun s e -> mk_typschm $2 (mk_typ (ATyp_fn ($4, $6, $8)) s e) s e) $startpos $endpos }
  | typ Bidir typ
    { (fun s e -> mk_typschm mk_typqn (mk_typ (ATyp_bidir ($1, $3)) s e) s e) $startpos $endpos }
  | Forall typquant Dot typ Bidir typ
    { (fun s e -> mk_typschm $2 (mk_typ (ATyp_bidir ($4, $6)) s e) s e) $startpos $endpos }

typschm_eof:
  | typschm Eof
    { $1 }

pat_string_append:
  | atomic_pat
    { [$1] }
  | atomic_pat Caret pat_string_append
    { $1 :: $3 }

pat1:
  | atomic_pat
    { $1 }
  (* | atomic_pat Bar pat1
    { mk_pat (P_or ($1, $3)) $startpos $endpos } *)
  | atomic_pat At pat_concat
    { mk_pat (P_vector_concat ($1 :: $3)) $startpos $endpos }
  | atomic_pat ColonColon pat1
    { mk_pat (P_cons ($1, $3)) $startpos $endpos }
  | atomic_pat Caret pat_string_append
    { mk_pat (P_string_append ($1 :: $3)) $startpos $endpos }

pat_concat:
  | atomic_pat
    { [$1] }
  | atomic_pat At pat_concat
    { $1 :: $3 }

pat:
  | pat1
    { $1 }
  | pat1 As typ
    { mk_pat (P_var ($1, $3)) $startpos $endpos }
  | pat1 Match typ
    { mk_pat (P_var ($1, $3)) $startpos $endpos }

pat_list:
  | pat
    { [$1] }
  | pat Comma pat_list
    { $1 :: $3 }

atomic_pat:
  | Under
    { mk_pat (P_wild) $startpos $endpos }
  | lit
    { mk_pat (P_lit $1) $startpos $endpos }
  | id
    { mk_pat (P_id $1) $startpos $endpos }
  | kid
    { mk_pat (P_var (mk_pat (P_id (id_of_kid $1)) $startpos $endpos,
		     mk_typ (ATyp_var $1) $startpos $endpos)) $startpos $endpos }
  | id Unit
    { mk_pat (P_app ($1, [mk_pat (P_lit (mk_lit L_unit $startpos $endpos)) $startpos $endpos])) $startpos $endpos }
  | id Lparen pat_list Rparen
    { mk_pat (P_app ($1, $3)) $startpos $endpos }
  | atomic_pat Colon typ
    { mk_pat (P_typ ($3, $1)) $startpos $endpos }
  | Lparen pat Rparen
    { $2 }
  | Lparen pat Comma pat_list Rparen
    { mk_pat (P_tup ($2 :: $4)) $startpos $endpos }
  | Lsquare pat_list Rsquare
    { mk_pat (P_vector $2) $startpos $endpos }
  | LsquareBar RsquareBar
    { mk_pat (P_list []) $startpos $endpos }
  | LsquareBar pat_list RsquareBar
    { mk_pat (P_list $2) $startpos $endpos }

lit:
  | True
    { mk_lit L_true $startpos $endpos }
  | False
    { mk_lit L_false $startpos $endpos }
  | Unit
    { mk_lit L_unit $startpos $endpos }
  | Num
    { mk_lit (L_num $1) $startpos $endpos }
  | Undefined
    { mk_lit L_undef $startpos $endpos }
  | Bitzero
    { mk_lit L_zero $startpos $endpos }
  | Bitone
    { mk_lit L_one $startpos $endpos }
  | Bin
    { mk_lit (L_bin $1) $startpos $endpos }
  | Hex
    { mk_lit (L_hex $1) $startpos $endpos }
  | String
    { mk_lit (L_string $1) $startpos $endpos }
  | Real
    { mk_lit (L_real $1) $startpos $endpos }

exp_eof:
  | exp Eof
    { $1 }

exp:
  | exp0
    { $1 }
  | atomic_exp Eq exp
    { mk_exp (E_assign ($1, $3)) $startpos $endpos }
  | Let_ letbind In exp
    { mk_exp (E_let ($2, $4)) $startpos $endpos }
  | Var atomic_exp Eq exp In exp
    { mk_exp (E_var ($2, $4, $6)) $startpos $endpos }
  | Star atomic_exp
    { mk_exp (E_deref $2) $startpos $endpos }
  | Lcurly block Rcurly
    { mk_exp (E_block $2) $startpos $endpos }
  | Return exp
    { mk_exp (E_return $2) $startpos $endpos }
  | Throw exp
    { mk_exp (E_throw $2) $startpos $endpos }
  | If_ exp Then exp Else exp
    { mk_exp (E_if ($2, $4, $6)) $startpos $endpos }
  | If_ exp Then exp
    { mk_exp (E_if ($2, $4, mk_lit_exp L_unit $endpos($4) $endpos($4))) $startpos $endpos }
  | Match exp Lcurly case_list Rcurly
    { mk_exp (E_case ($2, $4)) $startpos $endpos }
  | Try exp Catch Lcurly case_list Rcurly
    { mk_exp (E_try ($2, $5)) $startpos $endpos }
  | Foreach Lparen id Id atomic_exp Id atomic_exp By atomic_exp In typ Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"from\" in foreach loop"));
      if $6 <> "to" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"to\" in foreach loop"));
      mk_exp (E_for ($3, $5, $7, $9, $11, $13)) $startpos $endpos }
  | Foreach Lparen id Id atomic_exp Id atomic_exp By atomic_exp Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"from\" in foreach loop"));
      if $6 <> "to" && $6 <> "downto" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"to\" or \"downto\" in foreach loop"));
      let order =
        if $6 = "to"
        then ATyp_aux(ATyp_inc,loc $startpos($6) $endpos($6))
        else ATyp_aux(ATyp_dec,loc $startpos($6) $endpos($6))
      in
      mk_exp (E_for ($3, $5, $7, $9, order, $11)) $startpos $endpos }
  | Foreach Lparen id Id atomic_exp Id atomic_exp Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"from\" in foreach loop"));
      if $6 <> "to" && $6 <> "downto" then
       raise (Parse_error_locn (loc $startpos $endpos,"Missing \"to\" or \"downto\" in foreach loop"));
      let step = mk_lit_exp (L_num (Big_int.of_int 1)) $startpos $endpos in
      let ord =
        if $6 = "to"
        then ATyp_aux(ATyp_inc,loc $startpos($6) $endpos($6))
        else ATyp_aux(ATyp_dec,loc $startpos($6) $endpos($6))
      in
      mk_exp (E_for ($3, $5, $7, step, ord, $9)) $startpos $endpos }
  | Repeat exp Until exp
    { mk_exp (E_loop (Until, $4, $2)) $startpos $endpos }
  | While exp Do exp
    { mk_exp (E_loop (While, $2, $4)) $startpos $endpos }

/* The following implements all nine levels of user-defined precedence for
operators in expressions, with both left, right and non-associative operators */

exp0:
  | exp1 op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp0l op0l exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 op0r exp0r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }
exp0l:
  | exp1 op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp0l op0l exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }
exp0r:
  | exp1 op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 op0r exp0r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }

exp1:
  | exp2 op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1l op1l exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 op1r exp1r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }
exp1l:
  | exp2 op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1l op1l exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }
exp1r:
  | exp2 op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 op1r exp1r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }

exp2:
  | exp3 op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2l op2l exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 op2r exp2r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 Bar exp2r { mk_exp (E_app_infix ($1, mk_id (Id "|") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp3 { $1 }
exp2l:
  | exp3 op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2l op2l exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 { $1 }
exp2r:
  | exp3 op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 op2r exp2r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 Bar exp2r { mk_exp (E_app_infix ($1, mk_id (Id "|") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp3 { $1 }

exp3:
  | exp4 op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3l op3l exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 op3r exp3r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 Amp exp3r { mk_exp (E_app_infix ($1, mk_id (Id "&") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp4 { $1 }
exp3l:
  | exp4 op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3l op3l exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 { $1 }
exp3r:
  | exp4 op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 op3r exp3r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 Amp exp3r { mk_exp (E_app_infix ($1, mk_id (Id "&") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp4 { $1 }

exp4:
  | exp5 op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 Lt exp5 { mk_exp (E_app_infix ($1, mk_id (Id "<") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 Gt exp5 { mk_exp (E_app_infix ($1, mk_id (Id ">") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 LtEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id "<=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 GtEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id ">=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 ExclEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id "!=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 EqEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id "==") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp4l op4l exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 op4r exp4r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }
exp4l:
  | exp5 op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4l op4l exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }
exp4r:
  | exp5 op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 op4r exp4r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }

exp5:
  | exp6 op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5l op5l exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 op5r exp5r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 At exp5r { mk_exp (E_vector_append ($1, $3)) $startpos $endpos }
  | exp6 ColonColon exp5r { mk_exp (E_cons ($1, $3)) $startpos $endpos }
  | exp6 { $1 }
exp5l:
  | exp6 op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5l op5l exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 { $1 }
exp5r:
  | exp6 op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 op5r exp5r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 At exp5r { mk_exp (E_vector_append ($1, $3)) $startpos $endpos }
  | exp6 ColonColon exp5r { mk_exp (E_cons ($1, $3)) $startpos $endpos }
  | exp6 { $1 }

exp6:
  | exp7 op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l op6l exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 op6r exp6r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Plus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "+") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp6l Minus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "-") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp7 { $1 }
exp6l:
  | exp7 op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l op6l exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Plus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "+") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp6l Minus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "-") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp7 { $1 }
exp6r:
  | exp7 op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 op6r exp6r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 { $1 }

exp7:
  | exp8 op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l op7l exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 op7r exp7r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Star exp8 { mk_exp (E_app_infix ($1, mk_id (Id "*") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp8 { $1 }
exp7l:
  | exp8 op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l op7l exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Star exp8 { mk_exp (E_app_infix ($1, mk_id (Id "*") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp8 { $1 }
exp7r:
  | exp8 op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 op7r exp7r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 { $1 }

exp8:
  | exp9 op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8l op8l exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 op8r exp8r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 Caret exp8r { mk_exp (E_app_infix ($1, mk_id (Id "^") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }
exp8l:
  | exp9 op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8l op8l exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }
exp8r:
  | exp9 op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 op8r exp8r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 Caret exp8r { mk_exp (E_app_infix ($1, mk_id (Id "^") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }

exp9:
  | atomic_exp op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9l op9l atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp op9r exp9r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }
exp9l:
  | atomic_exp op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9l op9l atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }
exp9r:
  | atomic_exp op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp op9r exp9r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }

case:
  | pat EqGt exp
    { mk_pexp (Pat_exp ($1, $3)) $startpos $endpos }
  | pat If_ exp EqGt exp
    { mk_pexp (Pat_when ($1, $3, $5)) $startpos $endpos }

case_list:
  | case
    { [$1] }
  | case Comma case_list
    { $1 :: $3 }

block:
  | exp
    { [$1] }
  | Let_ letbind Semi block
    { [mk_exp (E_let ($2, mk_exp (E_block $4) $startpos($4) $endpos)) $startpos $endpos] }
  | Var atomic_exp Eq exp Semi block
    { [mk_exp (E_var ($2, $4, mk_exp (E_block $6) $startpos($6) $endpos)) $startpos $endpos] }
  | exp Semi /* Allow trailing semicolon in block */
    { [$1] }
  | exp Semi block
    { $1 :: $3 }

%inline letbind:
  | pat Eq exp
    { LB_aux (LB_val ($1, $3), loc $startpos $endpos) }

atomic_exp:
  | atomic_exp Colon atomic_typ
    { mk_exp (E_cast ($3, $1)) $startpos $endpos }
  | lit
    { mk_exp (E_lit $1) $startpos $endpos }
  | id MinusGt id Unit
    { mk_exp (E_app (prepend_id "_mod_" $3, [mk_exp (E_ref $1) $startpos($1) $endpos($1)])) $startpos $endpos }
  | id MinusGt id Lparen exp_list Rparen
    { mk_exp (E_app (prepend_id "_mod_" $3, mk_exp (E_ref $1) $startpos($1) $endpos($1) :: $5)) $startpos $endpos }
  | atomic_exp Dot id Unit
    { mk_exp (E_app (prepend_id "_mod_" $3, [$1])) $startpos $endpos }
  | atomic_exp Dot id Lparen exp_list Rparen
    { mk_exp (E_app (prepend_id "_mod_" $3, $1 :: $5)) $startpos $endpos }
  | atomic_exp Dot id
    { mk_exp (E_field ($1, $3)) $startpos $endpos }
  | id
    { mk_exp (E_id $1) $startpos $endpos }
  | kid
    { mk_exp (E_sizeof (mk_typ (ATyp_var $1) $startpos $endpos)) $startpos $endpos }
  | Ref id
    { mk_exp (E_ref $2) $startpos $endpos }
  | id Unit
    { mk_exp (E_app ($1, [mk_lit_exp L_unit $startpos($2) $endpos])) $startpos $endpos }
  | id Lparen exp_list Rparen
    { mk_exp (E_app ($1, $3)) $startpos $endpos }
  | Exit Unit
    { mk_exp (E_exit (mk_lit_exp L_unit $startpos $endpos)) $startpos $endpos }
  | Exit Lparen exp Rparen
    { mk_exp (E_exit $3) $startpos $endpos }
  | Sizeof Lparen typ Rparen
    { mk_exp (E_sizeof $3) $startpos $endpos }
  | Constraint Lparen typ Rparen
    { mk_exp (E_constraint $3) $startpos $endpos }
  | Assert Lparen exp Rparen
    { mk_exp (E_assert ($3, mk_lit_exp (L_string "") $startpos($4) $endpos($4))) $startpos $endpos }
  | Assert Lparen exp Comma exp Rparen
    { mk_exp (E_assert ($3, $5)) $startpos $endpos }
  | atomic_exp Lsquare exp Rsquare
    { mk_exp (E_vector_access ($1, $3)) $startpos $endpos }
  | atomic_exp Lsquare exp DotDot exp Rsquare
    { mk_exp (E_vector_subrange ($1, $3, $5)) $startpos $endpos }
  | atomic_exp Lsquare exp Comma exp Rsquare
    { mk_exp (E_app (mk_id (Id "slice") $startpos($2) $endpos, [$1; $3; $5])) $startpos $endpos }
  | Struct Lcurly fexp_exp_list Rcurly
    { mk_exp (E_record $3) $startpos $endpos }
  | Lcurly exp With fexp_exp_list Rcurly
    { mk_exp (E_record_update ($2, $4)) $startpos $endpos }
  | Lsquare exp_list Rsquare
    { mk_exp (E_vector $2) $startpos $endpos }
  | Lsquare exp With atomic_exp Eq exp Rsquare
    { mk_exp (E_vector_update ($2, $4, $6)) $startpos $endpos }
  | Lsquare exp With atomic_exp DotDot atomic_exp Eq exp Rsquare
    { mk_exp (E_vector_update_subrange ($2, $4, $6, $8)) $startpos $endpos }
  | LsquareBar RsquareBar
    { mk_exp (E_list []) $startpos $endpos }
  | LsquareBar exp_list RsquareBar
    { mk_exp (E_list $2) $startpos $endpos }
  | Lparen exp Rparen
    { $2 }
  | Lparen exp Comma exp_list Rparen
    { mk_exp (E_tuple ($2 :: $4)) $startpos $endpos }

fexp_exp:
  | atomic_exp Eq exp
    { mk_exp (E_app_infix ($1, mk_id (Id "=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | TildeTilde id
    { mk_exp (E_app_infix (mk_exp (E_id $2) $startpos($2) $endpos($2), mk_id (Id "=") $startpos $endpos, mk_exp (E_id $2) $startpos($2) $endpos($2))) $startpos $endpos }

fexp_exp_list:
  | fexp_exp
    { [$1] }
  | fexp_exp Comma fexp_exp_list
    { $1 :: $3 }

exp_list:
  | exp
    { [$1] }
  | exp Comma exp_list
    { $1 :: $3 }

funcl_patexp:
  | pat Eq exp
    { mk_pexp (Pat_exp ($1, $3)) $startpos $endpos }
  | Lparen pat If_ exp Rparen Eq exp
    { mk_pexp (Pat_when ($2, $4, $7)) $startpos $endpos }

funcl_patexp_typ:
  | pat Eq exp
    { (mk_pexp (Pat_exp ($1, $3)) $startpos $endpos, mk_tannotn) }
  | pat MinusGt typ Eq exp
    { (mk_pexp (Pat_exp ($1, $5)) $startpos $endpos, mk_tannot mk_typqn $3 $startpos $endpos($3)) }
  | Forall typquant Dot pat MinusGt typ Eq exp
    { (mk_pexp (Pat_exp ($4, $8)) $startpos $endpos, mk_tannot $2 $6 $startpos $endpos($6)) }
  | Lparen pat If_ exp Rparen Eq exp
    { (mk_pexp (Pat_when ($2, $4, $7)) $startpos $endpos, mk_tannotn) }
  | Forall typquant Dot Lparen pat If_ exp Rparen MinusGt typ Eq exp
    { (mk_pexp (Pat_when ($5, $7, $12)) $startpos $endpos, mk_tannot $2 $10 $startpos $endpos($10)) }

funcl:
  | id funcl_patexp
    { mk_funcl (FCL_Funcl ($1, $2)) $startpos $endpos }

funcls2:
  | id funcl_patexp
    { [mk_funcl (FCL_Funcl ($1, $2)) $startpos $endpos] }
  | id funcl_patexp And funcls2
    { mk_funcl (FCL_Funcl ($1, $2)) $startpos $endpos($2) :: $4 }

funcls:
  | id funcl_patexp_typ
    { let pexp, tannot = $2 in ([mk_funcl (FCL_Funcl ($1, pexp)) $startpos $endpos], tannot) }
  | id funcl_patexp And funcls2
    { (mk_funcl (FCL_Funcl ($1, $2)) $startpos $endpos($2) :: $4, mk_tannotn) }

funcl_typ:
  | Forall typquant Dot typ
    { mk_tannot $2 $4 $startpos $endpos }
  | typ
    { mk_tannot mk_typqn $1 $startpos $endpos }

index_range:
  | Num
    { mk_ir (BF_single $1) $startpos $endpos }
  | Num DotDot Num
    { mk_ir (BF_range ($1, $3)) $startpos $endpos }

r_id_def:
  | id Colon index_range
    { $1, $3 }

r_def_body:
  | r_id_def
    { [$1] }
  | r_id_def Comma
    { [$1] }
  | r_id_def Comma r_def_body
    { $1 :: $3 }

param_kopt:
  | kid Colon kind
    { KOpt_aux (KOpt_kind ($3, $1), loc $startpos $endpos) }
  | kid
    { KOpt_aux (KOpt_none $1, loc $startpos $endpos) }

param_kopt_list:
  | param_kopt
    { [$1] }
  | param_kopt Comma param_kopt_list
    { $1 :: $3 }

typaram:
  | Lparen param_kopt_list Rparen Comma typ
    { let qi_nc = QI_aux (QI_const $5, loc $startpos($5) $endpos($5)) in
      mk_typq $2 [qi_nc] $startpos $endpos }
  | Lparen param_kopt_list Rparen
    { mk_typq $2 [] $startpos $endpos }

type_def:
  | Typedef id typaram Eq typ
    { mk_td (TD_abbrev ($2, $3, K_aux (K_type, Parse_ast.Unknown), $5)) $startpos $endpos }
  | Typedef id Eq typ
    { mk_td (TD_abbrev ($2, mk_typqn, K_aux (K_type, Parse_ast.Unknown), $4)) $startpos $endpos }
  | Typedef id typaram MinusGt kind Eq typ
    { mk_td (TD_abbrev ($2, $3, $5, $7)) $startpos $endpos }
  | Typedef id Colon kind Eq typ
    { mk_td (TD_abbrev ($2, mk_typqn, $4, $6)) $startpos $endpos }
  | Struct id Eq Lcurly struct_fields Rcurly
    { mk_td (TD_record ($2, mk_namesectn, TypQ_aux (TypQ_tq [], loc $endpos($2) $startpos($3)), $5, false)) $startpos $endpos }
  | Struct id typaram Eq Lcurly struct_fields Rcurly
    { mk_td (TD_record ($2, mk_namesectn, $3, $6, false)) $startpos $endpos }
  | Enum id Eq enum_bar
    { mk_td (TD_enum ($2, mk_namesectn, $4, false)) $startpos $endpos }
  | Enum id Eq Lcurly enum Rcurly
    { mk_td (TD_enum ($2, mk_namesectn, $5, false)) $startpos $endpos }
  | Newtype id Eq type_union
    { mk_td (TD_variant ($2, mk_namesectn, TypQ_aux (TypQ_tq [], loc $endpos($2) $startpos($3)), [$4], false)) $startpos $endpos }
  | Newtype id typaram Eq type_union
    { mk_td (TD_variant ($2, mk_namesectn, $3, [$5], false)) $startpos $endpos }
  | Union id Eq Lcurly type_unions Rcurly
    { mk_td (TD_variant ($2, mk_namesectn, TypQ_aux (TypQ_tq [], loc $endpos($2) $startpos($3)), $5, false)) $startpos $endpos }
  | Union id typaram Eq Lcurly type_unions Rcurly
    { mk_td (TD_variant ($2, mk_namesectn, $3, $6, false)) $startpos $endpos }
  | Bitfield id Colon typ Eq Lcurly r_def_body Rcurly
    { mk_td (TD_bitfield ($2, $4, $7)) $startpos $endpos }

enum_bar:
  | id
    { [$1] }
  | id Bar enum_bar
    { $1 :: $3 }

enum:
  | id
    { [$1] }
  | id Comma enum
    { $1 :: $3 }

struct_field:
  | id Colon typ
    { ($3, $1) }

struct_fields:
  | struct_field
    { [$1] }
  | struct_field Comma
    { [$1] }
  | struct_field Comma struct_fields
    { $1 :: $3 }

type_union:
  | id Colon typ
    { Tu_aux (Tu_ty_id ($3, $1), loc $startpos $endpos) }
  | id Colon typ MinusGt typ
    { (fun s e -> Tu_aux (Tu_ty_id (mk_typ (ATyp_fn ($3, $5, mk_typ (ATyp_set []) s e)) s e, $1), loc s e)) $startpos $endpos }
  | id Colon Lcurly struct_fields Rcurly
    { Tu_aux (Tu_ty_anon_rec ($4, $1), loc $startpos $endpos) }

type_unions:
  | type_union
    { [$1] }
  | type_union Comma
    { [$1] }
  | type_union Comma type_unions
    { $1 :: $3 }

rec_measure:
  | Lcurly pat EqGt exp Rcurly
    { mk_recr (Rec_measure ($2, $4)) $startpos $endpos }

fun_def:
  | Function_ funcls
    { let funcls, tannot = $2 in mk_fun (FD_function (mk_recn, tannot, mk_eannotn, funcls)) $startpos $endpos }
  | Function_ rec_measure funcls
    { let funcls, tannot = $3 in mk_fun (FD_function ($2, tannot, mk_eannotn, funcls)) $startpos $endpos }

fun_def_list:
  | fun_def
    { [$1] }
  | fun_def fun_def_list
    { $1 :: $2 }

mpat_string_append:
  | atomic_mpat
    { [$1] }
  | atomic_mpat Caret mpat_string_append
    { $1 :: $3 }

mpat:
  | atomic_mpat
    { $1 }
  | atomic_mpat As id
    { mk_mpat (MP_as ($1, $3)) $startpos $endpos }
  | atomic_mpat At mpat_concat
    { mk_mpat (MP_vector_concat ($1 :: $3)) $startpos $endpos }
  | atomic_mpat ColonColon mpat
    { mk_mpat (MP_cons ($1, $3)) $startpos $endpos }
  | atomic_mpat Caret mpat_string_append
    { mk_mpat (MP_string_append ($1 :: $3)) $startpos $endpos }

mpat_concat:
  | atomic_mpat
    { [$1] }
  | atomic_mpat At mpat_concat
    { $1 :: $3 }

mpat_list:
  | mpat
    { [$1] }
  | mpat Comma mpat_list
    { $1 :: $3 }

atomic_mpat:
  | lit
    { mk_mpat (MP_lit $1) $startpos $endpos }
  | id
    { mk_mpat (MP_id $1) $startpos $endpos }
  | id Unit
    { mk_mpat (MP_app ($1, [mk_mpat (MP_lit (mk_lit L_unit $startpos($2) $endpos($2))) $startpos($2) $endpos($2)])) $startpos $endpos }
  | id Lparen mpat_list Rparen
    { mk_mpat (MP_app ($1, $3)) $startpos $endpos }
  | Lparen mpat Rparen
    { $2 }
  | Lparen mpat Comma mpat_list Rparen
    { mk_mpat (MP_tup ($2 :: $4)) $startpos $endpos }
  | Lsquare mpat_list Rsquare
    { mk_mpat (MP_vector $2) $startpos $endpos }
  | LsquareBar RsquareBar
    { mk_mpat (MP_list []) $startpos $endpos }
  | LsquareBar mpat_list RsquareBar
    { mk_mpat (MP_list $2) $startpos $endpos }
  | atomic_mpat Colon typ
    { mk_mpat (MP_typ ($1, $3)) $startpos $endpos }



%inline mpexp:
  | mpat
    { mk_mpexp (MPat_pat $1) $startpos $endpos }
  | mpat If_ exp
    { mk_mpexp (MPat_when ($1, $3)) $startpos $endpos }


mapcl:
  | mpexp Bidir mpexp
    { mk_bidir_mapcl $1 $3 $startpos $endpos }
  | mpexp EqGt exp
      { mk_forwards_mapcl $1 $3 $startpos $endpos }
  | mpexp LtMinus exp
      { mk_backwards_mapcl $1 $3 $startpos $endpos }
  (* | exp LtMinus pat
   *   { mk_backwards_mapcl (mk_pexp (Pat_exp ($3, $1)) $startpos $endpos) $startpos $endpos }
   * | exp LtMinus pat If_ exp
   *   { mk_backwards_mapcl (mk_pexp (Pat_when ($3, $5, $1)) $startpos $endpos) $startpos $endpos } *)

mapcl_list:
  | mapcl
    { [$1] }
  | mapcl Comma mapcl_list
    { $1 :: $3 }

map_def:
  | Mapping id Eq Lcurly mapcl_list Rcurly
    { mk_map $2 mk_typschm_opt_none $5 $startpos $endpos }
  | Mapping id Colon typschm Eq Lcurly mapcl_list Rcurly
    { mk_map $2 (mk_typschm_opt $4 $startpos($4) $endpos($4)) $7 $startpos $endpos }

let_def:
  | Let_ letbind
    { $2 }

externs:
  | id Colon String
    { ([(string_of_id $1, $3)], None) }
  | Under Colon String
    { ([], Some $3) }
  | id Colon String Comma externs
    { cons_fst (string_of_id $1, $3) $5 }

val_spec_def:
  | Doc val_spec_def
    { doc_vs $1 $2 }
  | Val id Colon typschm
    { mk_vs (VS_val_spec ($4, $2, (fun _ -> None), false)) $startpos $endpos }
  | Val Cast id Colon typschm
    { mk_vs (VS_val_spec ($5, $3, (fun _ -> None), true)) $startpos $endpos }
  | Val id Eq String Colon typschm
    { mk_vs (VS_val_spec ($6, $2, (fun _ -> Some $4), false)) $startpos $endpos }
  | Val Cast id Eq String Colon typschm
    { mk_vs (VS_val_spec ($7, $3, (fun _ -> Some $5), true)) $startpos $endpos }
  | Val String Colon typschm
    { mk_vs (VS_val_spec ($4, mk_id (Id $2) $startpos($2) $endpos($2), (fun _ -> Some $2), false)) $startpos $endpos }
  | Val Cast String Colon typschm
    { mk_vs (VS_val_spec ($5, mk_id (Id $3) $startpos($3) $endpos($3), (fun _ -> Some $3), true)) $startpos $endpos }
  | Val id Eq Lcurly externs Rcurly Colon typschm
    { mk_vs (VS_val_spec ($8, $2, (fun backend -> (assoc_opt backend $5)), false)) $startpos $endpos }
  | Val Cast id Eq Lcurly externs Rcurly Colon typschm
    { mk_vs (VS_val_spec ($9, $3, (fun backend -> (assoc_opt backend $6)), true)) $startpos $endpos }

register_def:
  | Register id Colon typ
    { mk_reg_dec (DEC_reg ($4, $2)) $startpos $endpos }
  | Register Configuration id Colon typ Eq exp
    { mk_reg_dec (DEC_config ($3, $5, $7)) $startpos $endpos }

default_def:
  | Default kind Inc
    { mk_default (DT_order ($2, mk_typ ATyp_inc $startpos($3) $endpos)) $startpos $endpos }
  | Default kind Dec
    { mk_default (DT_order ($2, mk_typ ATyp_dec $startpos($3) $endpos)) $startpos $endpos }

scattered_def:
  | Union id typaram
    { mk_sd (SD_variant($2, mk_namesectn, $3)) $startpos $endpos }
  | Union id
    { mk_sd (SD_variant($2, mk_namesectn, mk_typqn)) $startpos $endpos }
  | Function_ id
    { mk_sd (SD_function(mk_recn, mk_tannotn, mk_eannotn, $2)) $startpos $endpos }
  | Mapping id
    { mk_sd (SD_mapping ($2, mk_tannotn)) $startpos $endpos }
  | Mapping id Colon funcl_typ
    { mk_sd (SD_mapping ($2, $4)) $startpos $endpos }

scattered_clause:
  | Doc Function_ Clause funcl
    { mk_sd_doc (SD_funcl $4) $1 $startpos($2) $endpos }
  | Function_ Clause funcl
    { mk_sd (SD_funcl $3) $startpos $endpos }


def:
  | fun_def
    { DEF_fundef $1 }
  | map_def
    { DEF_mapdef $1 }
  | Fixity
    { let (prec, n, op) = $1 in DEF_fixity (prec, n, Id_aux (Id op, loc $startpos $endpos)) }
  | val_spec_def
    { DEF_spec $1 }
  | type_def
    { DEF_type $1 }
  | let_def
    { DEF_val $1 }
  | register_def
    { DEF_reg_dec $1 }
  | Overload id Eq Lcurly id_list Rcurly
    { DEF_overload ($2, $5) }
  | Overload id Eq enum_bar
    { DEF_overload ($2, $4) }
  | Scattered scattered_def
    { DEF_scattered $2 }
  | scattered_clause
    { DEF_scattered $1 }
  | Union Clause id Eq type_union
    { DEF_scattered (mk_sd (SD_unioncl ($3, $5)) $startpos $endpos) }
  | Mapping Clause id Eq mapcl
    { DEF_scattered (mk_sd (SD_mapcl ($3, $5)) $startpos $endpos) }
  | End id
    { DEF_scattered (mk_sd (SD_end $2) $startpos $endpos) }
  | default_def
    { DEF_default $1 }
  | Constant id Eq typ
    { DEF_kind (KD_aux (KD_nabbrev (K_aux (K_int, loc $startpos($1) $endpos($1)), $2, mk_namesectn, $4),
			loc $startpos $endpos)) }
  | Mutual Lcurly fun_def_list Rcurly
    { DEF_internal_mutrec $3 }
  | Pragma
    { DEF_pragma (fst $1, snd $1, loc $startpos $endpos) }
  | TerminationMeasure id pat Eq exp
    { DEF_measure ($2, $3, $5) }

defs_list:
  | def
    { [$1] }
  | def defs_list
    { $1::$2 }

def_eof:
  | def Eof
    { $1 }

defs:
  | defs_list
    { (Defs $1) }

file:
  | defs Eof
    { $1 }
