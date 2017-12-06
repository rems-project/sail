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

open Big_int
open Parse_ast

let loc () = Range(Parsing.symbol_start_pos(),Parsing.symbol_end_pos())
let locn m n = Range(Parsing.rhs_start_pos m,Parsing.rhs_end_pos n)

let id_of_kid = function
  | Kid_aux (Var v, l) -> Id_aux (Id (String.sub v 1 (String.length v - 1)), l)

let idl i = Id_aux(i, loc())

let string_of_id = function
  | Id_aux (Id str, _) -> str
  | Id_aux (DeIid str, _) -> str

let efl e = BE_aux(e, loc())

let ploc p = P_aux(p,loc ())
let eloc e = E_aux(e,loc ())
let peloc pe = Pat_aux(pe,loc ())
let lbloc lb = LB_aux(lb,loc ())

let bkloc k = BK_aux(k,loc ())
let kloc k = K_aux(k,loc ())
let kiloc ki = KOpt_aux(ki,loc ())
let tloc t = ATyp_aux(t,loc ())
let tlocl t l1 l2 = ATyp_aux(t,locn l1 l2)
let lloc l = L_aux(l,loc ())
let ploc p = P_aux(p,loc ())
let fploc p = FP_aux(p,loc ())

let funclloc f = FCL_aux(f,loc ())
let typql t = TypQ_aux(t, loc())
let irloc r = BF_aux(r, loc())
let defloc df = DT_aux(df, loc())

let tdloc td = TD_aux(td, loc())
let kdloc kd = KD_aux(kd, loc())
let funloc fn = FD_aux(fn, loc())
let vloc v = VS_aux(v, loc ())
let sdloc sd = SD_aux(sd, loc ())
let dloc d = d

let mk_typschm tq t s e = TypSchm_aux((TypSchm_ts(tq,t)),(locn s e))
let mk_rec i = (Rec_aux((Rec_rec), locn i i))
let mk_recn _ = (Rec_aux((Rec_nonrec), Unknown))
let mk_typqn _ = (TypQ_aux(TypQ_no_forall,Unknown))
let mk_tannot tq t s e = Typ_annot_opt_aux(Typ_annot_opt_some(tq,t),(locn s e))
let mk_tannotn _ = Typ_annot_opt_aux(Typ_annot_opt_none,Unknown)
let mk_eannot e i = Effect_opt_aux((Effect_opt_effect(e)),(locn i i))
let mk_eannotn _ = Effect_opt_aux(Effect_opt_pure,Unknown)
let mk_namesectn _ = Name_sect_aux(Name_sect_none,Unknown)

let make_range_sugar_bounded typ1 typ2 =
  ATyp_app(Id_aux(Id("range"),Unknown),[typ1; typ2;])
let make_range_sugar typ1 =
  make_range_sugar_bounded (ATyp_aux(ATyp_constant(zero_big_int), Unknown)) typ1
let make_atom_sugar typ1 =
  ATyp_app(Id_aux(Id("atom"),Unknown),[typ1])

let make_r bot top =
  match bot,top with
    | ATyp_aux(ATyp_constant b,_),ATyp_aux(ATyp_constant t,l) ->
      ATyp_aux(ATyp_constant (add_big_int (sub_big_int t b) unit_big_int),l)
    | bot,(ATyp_aux(_,l) as top) ->
      ATyp_aux((ATyp_sum ((ATyp_aux (ATyp_sum (top, ATyp_aux(ATyp_constant unit_big_int,Unknown)), Unknown)),
			  (ATyp_aux ((ATyp_neg bot),Unknown)))), l)				   

let make_vector_sugar_bounded order_set is_inc name typ typ1 typ2 = 
  let (rise,ord,name) = 
    if order_set 
    then if is_inc 
      then (make_r typ1 typ2,ATyp_inc,name) 
      else (make_r typ2 typ1,ATyp_dec,name) 
    else if name = "vector" 
    then (typ2, ATyp_default_ord,"vector_sugar_tb") (* rise not calculated, but top and bottom came from specification *)
    else (typ2, ATyp_default_ord,"vector_sugar_r") (* rise and base not calculated, rise only from specification *) in
  ATyp_app(Id_aux(Id(name),Unknown),[typ1;rise;ATyp_aux(ord,Unknown);typ])
let make_vector_sugar order_set is_inc typ typ1 =
  let zero = (ATyp_aux(ATyp_constant zero_big_int,Unknown)) in
  let (typ1,typ2) = match (order_set,is_inc,typ1) with
    | (true,true,ATyp_aux(ATyp_constant t,l)) -> zero,ATyp_aux(ATyp_constant (sub_big_int t unit_big_int),l)
    | (true,true,ATyp_aux(_, l)) -> zero,ATyp_aux (ATyp_sum (typ1,
    ATyp_aux(ATyp_neg(ATyp_aux(ATyp_constant unit_big_int,Unknown)), Unknown)), l)
    | (true,false,_) -> typ1,zero 
    | (false,_,_) -> zero,typ1 in
  make_vector_sugar_bounded order_set is_inc "vector_sugar_r" typ typ1 typ2

%}

/*Terminals with no content*/

%token And Alias As Assert Bitzero Bitone Bits By Case Clause Const Dec Def Default Deinfix Effect EFFECT End 
%token Enumerate Else Exit Extern False Forall Exist Foreach Overload Function_ If_ In IN Inc Let_ Member Nat NatNum Order Cast
%token Pure Rec Register Return Scattered Sizeof Struct Switch Then True TwoStarStar Type TYPE Typedef 
%token Undefined Union With When Val Constraint Try Catch Throw
%token Barr Depend Rreg Wreg Rmem Rmemt Wmem Wmv Wmvt Eamem Exmem Undef Unspec Nondet Escape
%token While Do Repeat Until


/* Avoid shift/reduce conflict - see right_atomic_exp rule */
%nonassoc Then
%nonassoc Else

%token Div_ Mod ModUnderS Quot Rem QuotUnderS

%token Bar Comma Dot Eof Minus Semi Under
%token Lcurly Rcurly Lparen Rparen Lsquare Rsquare
%token BarBar BarSquare BarBarSquare ColonEq ColonGt ColonSquare DotDot
%token MinusGt LtBar LtColon SquareBar SquareBarBar SquareColon

/*Terminals with content*/

%token <string> Id TyVar TyId
%token <Big_int.big_int> Num
%token <string> String Bin Hex Real

%token <string> Amp At Carrot  Div Eq Excl Gt Lt Plus Star Tilde
%token <string> AmpAmp CarrotCarrot Colon ColonColon EqEq ExclEq ExclExcl
%token <string> GtEq GtEqPlus GtGt GtGtGt GtPlus HashGtGt HashLtLt
%token <string> LtEq LtEqPlus LtGt LtLt LtLtLt LtPlus StarStar TildeCarrot

%token <string> GtEqUnderS GtEqUnderSi GtEqUnderU GtEqUnderUi GtGtUnderU GtUnderS
%token <string> GtUnderSi GtUnderU GtUnderUi LtEqUnderS LtEqUnderSi LtEqUnderU
%token <string> LtEqUnderUi LtUnderS LtUnderSi LtUnderU LtUnderUi StarStarUnderS StarStarUnderSi StarUnderS
%token <string> StarUnderSi StarUnderU StarUnderUi TwoCarrot PlusUnderS MinusUnderS 

%token <string> AmpI AtI CarrotI  DivI EqI ExclI GtI LtI PlusI StarI TildeI
%token <string> AmpAmpI CarrotCarrotI ColonColonI EqEqI ExclEqI ExclExclI
%token <string> GtEqI GtEqPlusI GtGtI GtGtGtI GtPlusI HashGtGtI HashLtLtI
%token <string> LtEqI LtEqPlusI LtGtI LtLtI LtLtLtI LtPlusI StarStarI TildeCarrotI

%token <string> GtEqUnderSI GtEqUnderSiI GtEqUnderUI GtEqUnderUiI GtGtUnderUI GtUnderSI
%token <string> GtUnderSiI GtUnderUI GtUnderUiI LtEqUnderSI LtEqUnderSiI LtEqUnderUI
%token <string> LtEqUnderUiI LtUnderSI LtUnderSiI LtUnderUI LtUnderUiI StarStarUnderSI StarStarUnderSiI StarUnderSI
%token <string> StarUnderSiI StarUnderUI StarUnderUiI TwoCarrotI


%start file nonempty_exp_list
%type <Parse_ast.defs> defs
%type <Parse_ast.atyp> typ
%type <Parse_ast.pat> pat
%type <Parse_ast.exp> exp
%type <Parse_ast.exp list> nonempty_exp_list
%type <Parse_ast.defs> file


%%

id:
  | Id
    { idl (Id($1)) }
  | Tilde
    { idl (Id($1)) }
  | Lparen Deinfix Amp Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix At Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Carrot Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Div Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Quot Rparen
    { idl (DeIid("quot")) }
  | Lparen Deinfix QuotUnderS Rparen
    { idl (DeIid("quot_s")) }
  | Lparen Deinfix Eq Rparen
    { Id_aux(DeIid($3),loc ()) }
  | Lparen Deinfix Excl Lparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Gt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Lt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtUnderS Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtUnderS Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Minus Rparen
    { idl (DeIid("-")) }
  | Lparen Deinfix MinusUnderS Rparen
    { idl (DeIid("-_s")) }
  | Lparen Deinfix Mod Rparen
    { idl (DeIid("mod")) }
  | Lparen Deinfix Plus Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix PlusUnderS Rparen
    { idl (DeIid("+_s")) }
  | Lparen Deinfix Star Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix StarUnderS Rparen
    { idl (DeIid("*_s")) }
  | Lparen Deinfix AmpAmp Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Bar Rparen
    { idl (DeIid("|")) }
  | Lparen Deinfix BarBar Rparen
    { idl (DeIid("||")) }
  | Lparen Deinfix CarrotCarrot Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Colon Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix ColonColon Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix EqEq Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix ExclEq Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix ExclExcl Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtEq Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtEqUnderS Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtEqPlus Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtGt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtGtGt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix GtPlus Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix HashGtGt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix HashLtLt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtEq Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtEqUnderS Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtLt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtLtLt Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix LtPlus Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix StarStar Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix Tilde Rparen
    { idl (DeIid($3)) }
  | Lparen Deinfix TildeCarrot Rparen
    { idl (DeIid($3)) }

tid:
  | TyId
    { (idl (Id($1))) }

tyvar:
  | TyVar
    { (Kid_aux((Var($1)),loc ())) }

tyvars:
  | tyvar
    { [$1] }
  | tyvar tyvars
    { $1 :: $2 }

atomic_kind:
  | TYPE
    { bkloc BK_type }
  | Nat
    { bkloc BK_nat }
  | NatNum
    { bkloc BK_nat }
  | Order
    { bkloc BK_order }

kind_help:
  | atomic_kind
    { [ $1 ] }
  | atomic_kind MinusGt kind_help
    { $1::$3 }

kind:
  | kind_help
    { K_aux(K_kind($1), loc ()) }

effect:
  | Barr
    { efl BE_barr }
  | Depend
    { efl BE_depend }
  | Rreg 
    { efl BE_rreg }
  | Wreg
    { efl BE_wreg }
  | Rmem
    { efl BE_rmem } 
  | Rmemt
    { efl BE_rmemt } 
  | Wmem
    { efl BE_wmem }
  | Wmv
    { efl BE_wmv }
  | Wmvt
    { efl BE_wmvt }
  | Eamem
    { efl BE_eamem }
  | Exmem
    { efl BE_exmem }
  | Undef
    { efl BE_undef }
  | Unspec
    { efl BE_unspec }
  | Nondet
      { efl BE_nondet }
  | Escape
      { efl BE_escape }

effect_list:
  | effect
    { [$1] }
  | effect Comma effect_list
    { $1::$3 }

effect_typ:
  | Lcurly effect_list Rcurly
    { tloc (ATyp_set($2)) }
  | Pure
    { tloc (ATyp_set([])) }

vec_typ:
  | tid Lsquare nexp_typ Rsquare
      { tloc (make_vector_sugar false false (ATyp_aux ((ATyp_id $1), locn 1 1)) $3) }
  | tid Lsquare nexp_typ Colon nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded false false "vector" (ATyp_aux ((ATyp_id $1), locn 1 1)) $3 $5) }
  | tid Lsquare nexp_typ LtColon nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded true true "vector" (ATyp_aux ((ATyp_id $1), locn 1 1)) $3 $5) }
  | tid Lsquare nexp_typ ColonGt nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded true false "vector" (ATyp_aux ((ATyp_id $1), locn 1 1)) $3 $5) }
  | tyvar Lsquare nexp_typ Rsquare
      { tloc (make_vector_sugar false false (ATyp_aux ((ATyp_var $1), locn 1 1)) $3) }
  | tyvar Lsquare nexp_typ Colon nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded false false "vector" (ATyp_aux ((ATyp_var $1), locn 1 1)) $3 $5) }
  | tyvar Lsquare nexp_typ LtColon nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded true true "vector" (ATyp_aux ((ATyp_var $1), locn 1 1)) $3 $5) }
  | tyvar Lsquare nexp_typ ColonGt nexp_typ Rsquare
      { tloc (make_vector_sugar_bounded true false "vector" (ATyp_aux ((ATyp_var $1), locn 1 1)) $3 $5) }

app_typs:
  | atomic_typ
    { [$1] }
  | atomic_typ Comma app_typs
    { $1::$3 }

atomic_typ:
  | vec_typ
    { $1 }
  | range_typ
    { $1 }
  | nexp_typ
    { $1 }
  | Inc
    { tloc (ATyp_inc) }
  | Dec
    { tloc (ATyp_dec) }
  | tid Lt app_typs Gt
    { tloc (ATyp_app($1,$3)) }
  | Register Lt app_typs Gt
    { tloc (ATyp_app(Id_aux(Id "register", locn 1 1),$3)) }

range_typ:
  | SquareBar nexp_typ BarSquare
      { tloc (make_range_sugar $2) }
  | SquareBar nexp_typ Colon nexp_typ BarSquare
      { tloc (make_range_sugar_bounded $2 $4) }
  | SquareColon nexp_typ ColonSquare
      { tloc (make_atom_sugar $2) }

nexp_typ:
  | nexp_typ Plus nexp_typ2
    { tloc (ATyp_sum ($1, $3)) }
  | nexp_typ Minus nexp_typ2
    { tloc (ATyp_minus ($1, $3)) }
  | Minus nexp_typ2
    { tloc (ATyp_neg $2) }
  | nexp_typ2
    { $1 }

nexp_typ2:
  | nexp_typ2 Star nexp_typ3
    { tloc (ATyp_times ($1, $3)) }
  | nexp_typ3
    { $1 }

nexp_typ3:
  | TwoStarStar nexp_typ4
     { tloc (ATyp_exp $2) }
  | nexp_typ4
     { $1 }

nexp_typ4:
  | Num
    { tlocl (ATyp_constant $1) 1 1 }
  | tid
    { tloc (ATyp_id $1) }
  | Lcurly id Rcurly
    { tloc (ATyp_id $2) }
  | tyvar
    { tloc (ATyp_var $1) }
  | Lparen exist_typ Rparen
    { $2 }

tup_typ_list:
   | atomic_typ Comma atomic_typ
       { [$1;$3] }
   | atomic_typ Comma tup_typ_list
       { $1::$3 }

tup_typ:
   | atomic_typ
     { $1 }
   | Lparen tup_typ_list Rparen
     { tloc (ATyp_tup $2) }

exist_typ:
  | Exist tyvars Comma nexp_constraint Dot tup_typ
    { tloc (ATyp_exist ($2, $4, $6)) }
  | Exist tyvars Dot tup_typ
    { tloc (ATyp_exist ($2, NC_aux (NC_true, loc ()), $4)) }
  | tup_typ
    { $1 }

typ:
  | exist_typ
    { $1 }
  | tup_typ MinusGt exist_typ Effect effect_typ
    { tloc (ATyp_fn($1,$3,$5)) }

lit:
  | True
    { lloc L_true }
  | False
    { lloc L_false }
  | Num
    { lloc (L_num $1) }
  | String
    { lloc (L_string $1) }
  | Lparen Rparen
    { lloc L_unit }
  | Bin
    { lloc (L_bin $1) }
  | Hex
    { lloc (L_hex $1) }
  | Real
    { lloc (L_real $1) }
  | Undefined
    { lloc L_undef }
  | Bitzero
    { lloc L_zero }
  | Bitone
    { lloc L_one }

atomic_pat:
  | lit
    { ploc (P_lit $1) }
  | Under
    { ploc P_wild }
  | Lparen pat As id Rparen
    { ploc (P_as($2,$4)) }
  | Lparen exist_typ Rparen atomic_pat
    { ploc (P_typ($2,$4)) }
  | id
    { ploc (P_app($1,[])) }
  | tyvar
    { ploc (P_var (ploc (P_id (id_of_kid $1)), $1)) }
  | Lcurly fpats Rcurly
    { ploc (P_record((fst $2, snd $2))) }
  | Lsquare comma_pats Rsquare
    { ploc (P_vector($2)) }
  | Lsquare pat Rsquare
    { ploc (P_vector([$2])) }
  | Lsquare Rsquare
    { ploc (P_vector []) }
  | Lparen comma_pats Rparen
    { ploc (P_tup($2)) }
  | SquareBarBar BarBarSquare
    { ploc (P_list([])) }
  | SquareBarBar pat BarBarSquare
    { ploc (P_list([$2])) }
  | SquareBarBar semi_pats BarBarSquare
    { ploc (P_list($2)) }
  | atomic_pat ColonColon pat
    { ploc (P_cons ($1, $3)) }
  | Lparen pat Rparen
    { $2 }

app_pat:
  | atomic_pat
    { $1 }
  | id Lparen comma_pats Rparen
    { ploc (P_app($1,$3)) }
  | id Lparen pat Rparen
    { ploc (P_app($1,[$3])) }

pat_colons:
  | atomic_pat Colon atomic_pat
    { ([$1;$3]) }
  | atomic_pat Colon pat_colons
    { ($1::$3) }

pat:
  | app_pat
    { $1 }
  | pat_colons
    { ploc (P_vector_concat($1)) }

comma_pats:
  | atomic_pat Comma atomic_pat
    { [$1;$3] }
  | atomic_pat Comma comma_pats
    { $1::$3 }

semi_pats:
  | atomic_pat Semi atomic_pat
    { [$1;$3] }
  | atomic_pat Semi semi_pats
    { $1::$3 }

fpat:
  | id Eq pat
    { fploc (FP_Fpat($1,$3)) }

fpats:
  | fpat
    { ([$1], false) }
  | fpat Semi
    { ([$1], true) }
  | fpat Semi fpats
    { ($1::fst $3, snd $3) }

npat:
  | Num Eq pat
    { ($1,$3) }

npats:
  | npat
    { [$1] }
  | npat Comma npats
    { ($1::$3) }

atomic_exp:
  | Lcurly semi_exps Rcurly
    { eloc (E_block $2) }
  | Nondet Lcurly semi_exps Rcurly
    { eloc (E_nondet $3) }
  | id
    { eloc (E_id($1)) }
  | lit
    { eloc (E_lit($1)) }
  | Lparen exp Rparen
    { $2 }
  | Lparen exist_typ Rparen atomic_exp
    { eloc (E_cast($2,$4)) }
  | Lparen comma_exps Rparen
    { eloc (E_tuple($2)) }
  | Lcurly exp With semi_exps Rcurly
    { eloc (E_record_update($2,$4)) } 
  | Lsquare Rsquare
    { eloc (E_vector([])) }
  | Lsquare exp Rsquare
    { eloc (E_vector([$2])) }
  | Lsquare comma_exps Rsquare
    { eloc (E_vector($2)) }
  | Lsquare exp With atomic_exp Eq exp Rsquare
    { eloc (E_vector_update($2,$4,$6)) }
  | Lsquare exp With atomic_exp Colon atomic_exp Eq exp Rsquare
    { eloc (E_vector_update_subrange($2,$4,$6,$8)) }
  | SquareBarBar BarBarSquare
      { eloc (E_list []) }
  | SquareBarBar exp BarBarSquare
      { eloc (E_list [$2]) }
  | SquareBarBar comma_exps BarBarSquare
    { eloc (E_list($2)) }
  | Switch exp Lcurly case_exps Rcurly
    { eloc (E_case($2,$4)) }
  | Try exp Catch Lcurly case_exps Rcurly
    { eloc (E_try ($2, $5)) }
  | Sizeof atomic_typ
    { eloc (E_sizeof($2)) }
  | Constraint Lparen nexp_constraint Rparen
    { eloc (E_constraint $3) }
  | Throw atomic_exp
    { eloc (E_throw $2) }
  | Exit atomic_exp
      { eloc (E_exit $2) }
  | Return atomic_exp
      { eloc (E_return $2) }
  | Assert Lparen exp Comma exp Rparen
      { eloc (E_assert ($3,$5)) }

field_exp:
  | atomic_exp
    { $1 }
  | atomic_exp Dot id
    { eloc (E_field($1,$3)) }

vaccess_exp:
  | field_exp
    { $1 }
  | atomic_exp Lsquare exp Rsquare
    { eloc (E_vector_access($1,$3)) }
  | atomic_exp Lsquare exp DotDot exp Rsquare
    { eloc (E_vector_subrange($1,$3,$5)) }

app_exp:
  | vaccess_exp
    { $1 }
  | id Lparen Rparen
    { eloc (E_app($1, [eloc (E_lit (lloc L_unit))])) }
  /* we wrap into a tuple here, but this is unwrapped in initial_check.ml */
  | id Lparen exp Rparen
    { eloc (E_app($1,[ E_aux((E_tuple [$3]),locn 3 3)])) }
  | id Lparen comma_exps Rparen
    { eloc (E_app($1,[E_aux (E_tuple $3,locn 3 3)])) }

right_atomic_exp:
  | If_ exp Then exp Else exp
    { eloc (E_if($2,$4,$6)) }
  | If_ exp Then exp
    { eloc (E_if($2,$4, eloc (E_lit(lloc L_unit)))) }
  | Foreach Lparen id Id atomic_exp Id atomic_exp By atomic_exp In typ Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn ((loc ()),"Missing \"from\" in foreach loop"));
      if $6 <> "to" then
       raise (Parse_error_locn ((loc ()),"Missing \"to\" in foreach loop"));
      eloc (E_for($3,$5,$7,$9,$11,$13)) }
  | Foreach Lparen id Id atomic_exp Id atomic_exp By atomic_exp Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn ((loc ()),"Missing \"from\" in foreach loop"));
      if $6 <> "to" && $6 <> "downto" then
       raise (Parse_error_locn ((loc ()),"Missing \"to\" or \"downto\" in foreach loop"));
      let order =
        if $6 = "to"
        then ATyp_aux(ATyp_inc,(locn 6 6))
        else ATyp_aux(ATyp_dec,(locn 6 6)) in
      eloc (E_for($3,$5,$7,$9,order,$11)) }
  | Foreach Lparen id Id atomic_exp Id atomic_exp Rparen exp
    { if $4 <> "from" then
       raise (Parse_error_locn ((loc ()),"Missing \"from\" in foreach loop"));
      if $6 <> "to" && $6 <> "downto" then
       raise (Parse_error_locn ((loc ()),"Missing \"to\" or \"downto\" in foreach loop"));
      let step = eloc (E_lit(lloc (L_num unit_big_int))) in
      let ord =
        if $6 = "to"
        then ATyp_aux(ATyp_inc,(locn 6 6))
        else ATyp_aux(ATyp_dec,(locn 6 6)) in
      eloc (E_for($3,$5,$7,step,ord,$9)) }
  | While exp Do exp
    { eloc (E_loop (While, $2, $4)) }
  | letbind In exp
    { eloc (E_let($1,$3)) }

starstar_exp:
  | app_exp
    { $1 }
  | starstar_exp StarStar app_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

/* this is where we diverge from the non-right_atomic path;
   here we go directly to right_atomic whereas the other one
   goes through app_exp, vaccess_exp and field_exp too. */
starstar_right_atomic_exp:
  | right_atomic_exp
    { $1 }
  | starstar_exp StarStar right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

star_exp:
  | starstar_exp
    { $1 }
  | star_exp Star starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp Div starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp Div_ starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id("div"), locn 2 2), $3)) }
  | star_exp Quot starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id("quot"), locn 2 2), $3)) }
  | star_exp QuotUnderS starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id("quot_s"), locn 2 2), $3)) }
  | star_exp Rem starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id("rem"), locn 2 2), $3)) }
  | star_exp Mod starstar_exp
      { eloc (E_app_infix($1,Id_aux(Id("mod"), locn 2 2), $3)) }
  | star_exp ModUnderS starstar_exp
      { eloc (E_app_infix($1,Id_aux(Id("mod_s"), locn 2 2), $3)) }
  | star_exp StarUnderS starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderSi starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderU starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderUi starstar_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

star_right_atomic_exp:
  | starstar_right_atomic_exp
    { $1 }
  | star_exp Star starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp Div starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp Div_ starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("div"), locn 2 2), $3)) }
  | star_exp Quot starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("quot"), locn 2 2), $3)) }
  | star_exp QuotUnderS starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("quot_s"), locn 2 2), $3)) }
  | star_exp Rem starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("rem"), locn 2 2), $3)) }
  | star_exp Mod starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("mod"), locn 2 2), $3)) }
  | star_exp ModUnderS starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("mod_s"), locn 2 2), $3)) }
  | star_exp StarUnderS starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderSi starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderU starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | star_exp StarUnderUi starstar_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

plus_exp:
  | star_exp
    { $1 }
  | plus_exp Plus star_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | plus_exp PlusUnderS star_exp
    { eloc (E_app_infix($1, Id_aux(Id($2), locn 2 2), $3)) }
  | plus_exp Minus star_exp
    { eloc (E_app_infix($1,Id_aux(Id("-"), locn 2 2), $3)) }
  | plus_exp MinusUnderS star_exp
    { eloc (E_app_infix($1,Id_aux(Id("-_s"),locn 2 2), $3)) }

plus_right_atomic_exp:
  | star_right_atomic_exp
    { $1 }
  | plus_exp Plus star_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | plus_exp Minus star_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("-"), locn 2 2), $3)) }
  | plus_exp PlusUnderS star_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | plus_exp MinusUnderS star_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("-_s"), locn 2 2), $3)) }

shift_exp:
  | plus_exp
    { $1 }
  | shift_exp GtGt plus_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp GtGtGt plus_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp LtLt plus_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp LtLtLt plus_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

shift_right_atomic_exp:
  | plus_right_atomic_exp
    { $1 }
  | shift_exp GtGt plus_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp GtGtGt plus_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp LtLt plus_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | shift_exp LtLtLt plus_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }


cons_exp:
  | shift_exp
    { $1 }
  | shift_exp ColonColon cons_exp
    { eloc (E_cons($1,$3)) }
  | shift_exp Colon cons_exp
    { eloc (E_vector_append($1, $3)) }

cons_right_atomic_exp:
  | shift_right_atomic_exp
    { $1 }
  | shift_exp ColonColon cons_right_atomic_exp
    { eloc (E_cons($1,$3)) }
  | shift_exp Colon cons_right_atomic_exp
    { eloc (E_vector_append($1, $3)) }

at_exp:
  | cons_exp
    { $1 }
  | cons_exp At at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp CarrotCarrot at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp Carrot at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp TildeCarrot at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

at_right_atomic_exp:
  | cons_right_atomic_exp
    { $1 }
  | cons_exp At at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp CarrotCarrot at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp Carrot at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | cons_exp TildeCarrot at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

eq_exp:
  | at_exp
    { $1 }
  /* XXX check for consistency */
  | eq_exp Eq at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp EqEq at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp ExclEq at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEq at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEqUnderS at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEqUnderU at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp Gt at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtUnderS at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtUnderU at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtEq at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtEqUnderS at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp Lt at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderS at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderSi at_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderU at_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  /* XXX assignement should not have the same precedence as equal,
  otherwise a := b > c requires extra parens... */
  | eq_exp ColonEq at_exp
    { eloc (E_assign($1,$3)) }

eq_right_atomic_exp:
  | at_right_atomic_exp
    { $1 }
  | eq_exp Eq at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp EqEq at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp ExclEq at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEq at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEqUnderS at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtEqUnderU at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp Gt at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtUnderS at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp GtUnderU at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtEq at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtEqUnderS at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp Lt at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderS at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderSi at_right_atomic_exp
    { eloc (E_app_infix ($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp LtUnderU at_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp ColonEq at_right_atomic_exp
    { eloc (E_assign($1,$3)) }

and_exp:
  | eq_exp
    { $1 }
  | eq_exp Amp and_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp AmpAmp and_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

and_right_atomic_exp:
  | eq_right_atomic_exp
    { $1 }
  | eq_exp Amp and_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }
  | eq_exp AmpAmp and_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id($2), locn 2 2), $3)) }

or_exp:
  | and_exp
    { $1 }
  | and_exp Bar or_exp
    { eloc (E_app_infix($1,Id_aux(Id("|"), locn 2 2), $3)) }
  | and_exp BarBar or_exp
    { eloc (E_app_infix($1,Id_aux(Id("||"), locn 2 2), $3)) }

or_right_atomic_exp:
  | and_right_atomic_exp
    { $1 }
  | and_exp Bar or_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("|"), locn 2 2), $3)) }
  | and_exp BarBar or_right_atomic_exp
    { eloc (E_app_infix($1,Id_aux(Id("||"), locn 2 2), $3)) }

exp:
  | or_exp
    { $1 }
  | or_right_atomic_exp
    { $1 }

comma_exps:
  | exp Comma exp
    { [$1;$3] }
  | exp Comma comma_exps
    { $1::$3 }

semi_exps_help:
  | exp
    { [$1] }
  | exp Semi
    { [$1] }
  | exp Semi semi_exps_help
    { $1::$3 }

semi_exps:
  |
    { [] }
  | semi_exps_help
    { $1 }

case_exp:
  | Case patsexp
    { $2 }

case_exps:
  | case_exp
    { [$1] }
  | case_exp case_exps
    { $1::$2 }

patsexp:
  | atomic_pat MinusGt exp
    { peloc (Pat_exp($1,$3)) }
  | atomic_pat When exp MinusGt exp
    { peloc (Pat_when ($1, $3, $5)) }

letbind:
  | Let_ atomic_pat Eq exp
    { lbloc (LB_val($2,$4)) }

funcl:
  | id atomic_pat Eq exp
    { funclloc (FCL_Funcl($1,$2,$4)) }

funcl_ands:
  | funcl
    { [$1] }
  | funcl And funcl_ands
    { $1::$3 }

/* This causes ambiguity because without a type quantifier it's unclear whether the first id is a function name or a type name for the optional types.*/
fun_def:
  | Function_ Rec typquant typ Effect effect_typ funcl_ands
    { funloc (FD_function(mk_rec 2, mk_tannot $3 $4 3 4, mk_eannot $6 6, $7)) }
  | Function_ Rec typquant typ funcl_ands
    { funloc (FD_function(mk_rec 2, mk_tannot $3 $4 3 4, mk_eannotn (), $5)) }
  | Function_ Rec typ Effect effect_typ funcl_ands
    { funloc (FD_function(mk_rec 2, mk_tannot (mk_typqn ()) $3 3 3, mk_eannot $5 5, $6)) }
  | Function_ Rec Effect effect_typ funcl_ands 
    { funloc (FD_function(mk_rec 2,mk_tannotn (), mk_eannot $4 4, $5)) }
  | Function_ Rec typ funcl_ands
    { funloc (FD_function(mk_rec 2,mk_tannot (mk_typqn ()) $3 3 3, mk_eannotn (), $4)) }
  | Function_ Rec funcl_ands
    { funloc (FD_function(mk_rec 2, mk_tannotn (), mk_eannotn (), $3)) }
  | Function_ typquant typ Effect effect_typ funcl_ands
    { funloc (FD_function(mk_recn (), mk_tannot $2 $3 2 3, mk_eannot $5 5, $6)) }
  | Function_ typquant typ funcl_ands
    { funloc (FD_function(mk_recn (), mk_tannot $2 $3 2 2, mk_eannotn (), $4)) }
  | Function_ typ Effect effect_typ funcl_ands
    { funloc (FD_function(mk_recn (), mk_tannot (mk_typqn ()) $2 2 2, mk_eannot $4 4, $5)) }
  | Function_ Effect effect_typ funcl_ands
    { funloc (FD_function(mk_recn (),mk_tannotn (), mk_eannot $3 3, $4)) }
  | Function_ typ funcl_ands
    { funloc (FD_function(mk_recn (),mk_tannot (mk_typqn ()) $2 2 2, mk_eannotn (), $3)) }
  | Function_ funcl_ands
    { funloc (FD_function(mk_recn (), mk_tannotn (), mk_eannotn (), $2)) }


val_spec:
  | Val typquant typ id
    { vloc (VS_val_spec(mk_typschm $2 $3 2 3,$4, (fun _ -> None), false)) }
  | Val typ id
    { vloc (VS_val_spec(mk_typschm (mk_typqn ()) $2 2 2,$3, (fun _ -> None), false)) }
  | Val Cast typquant typ id
    { vloc (VS_val_spec (mk_typschm $3 $4 3 4,$5, (fun _ -> None), true)) }
  | Val Cast typ id
    { vloc (VS_val_spec (mk_typschm (mk_typqn ()) $3 3 3, $4, (fun _ -> None), true)) }
  | Val Extern typquant typ id
    { vloc (VS_val_spec (mk_typschm $3 $4 3 4,$5, (fun _ -> Some (string_of_id $5)), false)) }
  | Val Extern typ id
    { vloc (VS_val_spec (mk_typschm (mk_typqn ()) $3 3 3, $4, (fun _ -> Some (string_of_id $4)), false)) }
  | Val Extern typquant typ id Eq String
    { vloc (VS_val_spec (mk_typschm $3 $4 3 4,$5, (fun _ -> Some $7), false)) }
  | Val Extern typ id Eq String
    { vloc (VS_val_spec (mk_typschm (mk_typqn ()) $3 3 3,$4, (fun _ -> Some $6), false)) }
  | Val Cast Extern typquant typ id
    { vloc (VS_val_spec (mk_typschm $4 $5 4 5,$6, (fun _ -> Some (string_of_id $6)), true)) }
  | Val Cast Extern typ id
    { vloc (VS_val_spec (mk_typschm (mk_typqn ()) $4 4 4, $5, (fun _ -> Some (string_of_id $5)), true)) }
  | Val Cast Extern typquant typ id Eq String
    { vloc (VS_val_spec (mk_typschm $4 $5 4 5,$6, (fun _ -> Some $8), true)) }
  | Val Cast Extern typ id Eq String
    { vloc (VS_val_spec (mk_typschm (mk_typqn ()) $4 4 4,$5, (fun _ -> Some $7), true)) }

kinded_id:
  | tyvar
    { kiloc (KOpt_none $1) }
  | kind tyvar
    { kiloc (KOpt_kind($1,$2))}

/*kinded_ids:
  | kinded_id
    { [$1] }
  | kinded_id kinded_ids
    { $1::$2 }*/

nums:
  | Num
    { [$1] }
  | Num Comma nums
    { $1::$3 }

nexp_constraint:
  | nexp_constraint1
    { $1 }
  | nexp_constraint1 Bar nexp_constraint
    { NC_aux (NC_or ($1, $3), loc ()) }

nexp_constraint1:
  | nexp_constraint2
    { $1 }
  | nexp_constraint2 Amp nexp_constraint1
    { NC_aux (NC_and ($1, $3), loc ()) }

nexp_constraint2:
  | nexp_typ Eq nexp_typ
    { NC_aux(NC_equal($1,$3), loc () ) }
  | nexp_typ ExclEq nexp_typ
    { NC_aux (NC_not_equal ($1, $3), loc ()) }
  | nexp_typ GtEq nexp_typ
    { NC_aux(NC_bounded_ge($1,$3), loc () ) }
  | nexp_typ LtEq nexp_typ
    { NC_aux(NC_bounded_le($1,$3), loc () ) }
  | tyvar In Lcurly nums Rcurly
    { NC_aux(NC_set($1,$4), loc ()) }
  | tyvar IN Lcurly nums Rcurly
    { NC_aux(NC_set($1,$4), loc ()) }
  | True
    { NC_aux (NC_true, loc ()) }
  | False
    { NC_aux (NC_false, loc ()) }
  | Lparen nexp_constraint Rparen
    { $2 }

id_constraint:
  | nexp_constraint
      { QI_aux((QI_const $1), loc())}
  | kinded_id
      { QI_aux((QI_id $1), loc()) }

id_constraints:
  | id_constraint
      { [$1] }
  | id_constraint Comma id_constraints
      { $1::$3 }

typquant:
  | Forall id_constraints Dot
    { typql(TypQ_tq($2)) }

name_sect:
  | Lsquare Id Eq String Rsquare
    {
      if $2 <> "name" then
       raise (Parse_error_locn ((loc ()),"Unexpected id \""^$2^"\" in name_sect (should be \"name\")"));
      Name_sect_aux(Name_sect_some($4), loc ()) }

c_def_body:
  | typ id
    { [($1,$2)],false }
  | typ id Semi
    { [($1,$2)],true }
  | typ id Semi c_def_body
    { ($1,$2)::(fst $4), snd $4 }

union_body:
  | id
    { [Tu_aux( Tu_id $1, loc())],false }
  | typ id
    { [Tu_aux( Tu_ty_id ($1,$2), loc())],false }
  | id Semi
    { [Tu_aux( Tu_id $1, loc())],true }
  | typ id Semi
    { [Tu_aux( Tu_ty_id ($1,$2),loc())],true }
  | id Semi union_body
    { (Tu_aux( Tu_id $1, loc()))::(fst $3), snd $3 }
  | typ id Semi union_body
    { (Tu_aux(Tu_ty_id($1,$2),loc()))::(fst $4), snd $4 }

index_range_atomic:
  | Num
    { irloc (BF_single($1)) }
  | Num DotDot Num
    { irloc (BF_range($1,$3)) }
  | Lparen index_range Rparen
    { $2 }

enum_body:
  | id
  { [$1] }
  | id Semi
  { [$1] }
  | id Semi enum_body
  { $1::$3 }

index_range:
  | index_range_atomic
    { $1 }
  | index_range_atomic Comma index_range
    { irloc(BF_concat($1,$3)) }

r_id_def:
  | index_range Colon id
    { $1,$3 }

r_def_body:
  | r_id_def
    { [$1] }
  | r_id_def Semi
    { [$1] }
  | r_id_def Semi r_def_body
    { $1::$3 }

type_def:
  | Typedef tid name_sect Eq typquant typ
    { tdloc (TD_abbrev($2,$3,mk_typschm $5 $6 5 6)) }
  | Typedef tid name_sect Eq typ
    { tdloc (TD_abbrev($2,$3,mk_typschm (mk_typqn ()) $5 5 5)) }
  | Typedef tid Eq typquant typ
    { tdloc (TD_abbrev($2,mk_namesectn (), mk_typschm $4 $5 4 5))}
  | Typedef tid Eq typ
    { tdloc (TD_abbrev($2,mk_namesectn (),mk_typschm (mk_typqn ()) $4 4 4)) }
  /* The below adds 4 shift/reduce conflicts. Due to c_def_body and confusions in id id and parens  */
  | Typedef tid name_sect Eq Const Struct typquant Lcurly c_def_body Rcurly
    { tdloc (TD_record($2,$3,$7,fst $9, snd $9)) }
  | Typedef tid name_sect Eq Const Struct Lcurly c_def_body Rcurly
    { tdloc (TD_record($2,$3,(mk_typqn ()), fst $8, snd $8)) }
  | Typedef tid Eq Const Struct typquant Lcurly c_def_body Rcurly
    { tdloc (TD_record($2,mk_namesectn (), $6, fst $8, snd $8)) }
  | Typedef tid Eq Const Struct Lcurly c_def_body Rcurly
    { tdloc (TD_record($2, mk_namesectn (), mk_typqn (), fst $7, snd $7)) }
  | Typedef tid name_sect Eq Const Union typquant Lcurly union_body Rcurly
    { tdloc (TD_variant($2,$3, $7, fst $9, snd $9)) }
  | Typedef tid Eq Const Union typquant Lcurly union_body Rcurly
    { tdloc (TD_variant($2,mk_namesectn (), $6, fst $8, snd $8)) }
  | Typedef tid name_sect Eq Const Union Lcurly union_body Rcurly
    { tdloc (TD_variant($2, $3, mk_typqn (), fst $8, snd $8)) }
  | Typedef tid Eq Const Union Lcurly union_body Rcurly
    { tdloc (TD_variant($2, mk_namesectn (), mk_typqn (), fst $7, snd $7)) }
  | Typedef tid Eq Enumerate Lcurly enum_body Rcurly
    { tdloc (TD_enum($2, mk_namesectn (), $6,false)) }
  | Typedef tid name_sect Eq Enumerate Lcurly enum_body Rcurly
    { tdloc (TD_enum($2,$3,$7,false)) }
  | Typedef tid Eq Register Bits Lsquare nexp_typ Colon nexp_typ Rsquare Lcurly r_def_body Rcurly
    { tdloc (TD_register($2, $7, $9, $12)) }

default_typ:
  | Default atomic_kind tyvar
    { defloc (DT_kind($2,$3)) }
  | Default atomic_kind Inc
    { defloc (DT_order($2, tloc (ATyp_inc))) }
  | Default atomic_kind Dec
    { defloc (DT_order($2, tloc (ATyp_dec))) }
  | Default typquant typ id
    { defloc (DT_typ((mk_typschm $2 $3 2 3),$4)) }
  | Default typ id
    { defloc (DT_typ((mk_typschm (mk_typqn ()) $2 2 2),$3)) }

scattered_def:
  | Function_ Rec typquant typ Effect effect_typ id
    { sdloc (SD_scattered_function(mk_rec 2, mk_tannot $3 $4 3 4, mk_eannot $6 6, $7)) }
  | Function_ Rec typ Effect effect_typ id
    { sdloc (SD_scattered_function(mk_rec 2, mk_tannot (mk_typqn ()) $3 3 3, mk_eannot $5 5, $6)) }
  | Function_ Rec typquant typ id
    { sdloc (SD_scattered_function(mk_rec 2, mk_tannot $3 $4 3 4, mk_eannotn (), $5)) }
  | Function_ Rec Effect effect_typ id
    { sdloc (SD_scattered_function (mk_rec 2, mk_tannotn (), mk_eannot $4 4, $5)) }
  | Function_ Rec typ id
    { sdloc (SD_scattered_function(mk_rec 2,mk_tannot (mk_typqn ()) $3 3 3, mk_eannotn (), $4)) }
  | Function_ Rec id
    { sdloc (SD_scattered_function(mk_rec 2,mk_tannotn (), mk_eannotn (),$3)) }
  | Function_ typquant typ Effect effect_typ id
    { sdloc (SD_scattered_function(mk_recn (),mk_tannot $2 $3 2 3, mk_eannot $5 5, $6)) }
  | Function_ typ Effect effect_typ id
    { sdloc (SD_scattered_function(mk_recn (), mk_tannot (mk_typqn ()) $2 2 2, mk_eannot $4 4, $5)) }
  | Function_ typquant typ id
    { sdloc (SD_scattered_function(mk_recn (), mk_tannot $2 $3 2 3, mk_eannotn (), $4)) }
  | Function_ Effect effect_typ id
    { sdloc (SD_scattered_function(mk_recn (), mk_tannotn (), mk_eannot $3 3, $4)) }
  | Function_ typ id
    { sdloc (SD_scattered_function(mk_recn (), mk_tannot (mk_typqn ()) $2 2 2, mk_eannotn (), $3)) }
  | Function_ id
    { sdloc (SD_scattered_function(mk_recn (), mk_tannotn (), mk_eannotn (), $2)) }
  | Typedef tid name_sect Eq Const Union typquant
    { sdloc (SD_scattered_variant($2,$3,$7)) }
  | Typedef tid Eq Const Union typquant
    { sdloc (SD_scattered_variant($2,(mk_namesectn ()),$6)) }
  | Typedef tid name_sect Eq Const Union
    { sdloc (SD_scattered_variant($2,$3,mk_typqn ())) }
  | Typedef tid Eq Const Union
    { sdloc (SD_scattered_variant($2,mk_namesectn (),mk_typqn ())) }

ktype_def:
  | Def kind tid name_sect Eq typquant typ
    { kdloc (KD_abbrev($2,$3,$4,mk_typschm $6 $7 6 7)) }
  | Def kind tid name_sect Eq typ
    { kdloc (KD_abbrev($2,$3,$4,mk_typschm (mk_typqn ()) $6 6 6)) }
  | Def kind tid Eq typquant typ
    { kdloc (KD_abbrev($2,$3,mk_namesectn (), mk_typschm $5 $6 5 6)) }
  | Def kind tid Eq typ
    { kdloc (KD_abbrev($2,$3,mk_namesectn (),mk_typschm (mk_typqn ()) $5 5 5)) }
  | Def kind tid Eq Num
    { kdloc (KD_abbrev($2,$3,mk_namesectn (),mk_typschm (mk_typqn ()) (tlocl (ATyp_constant $5) 5 5) 5 5)) }

def:
  | type_def
      { dloc (DEF_type($1)) }
  | ktype_def
      { dloc (DEF_kind($1)) }
  | fun_def
    { dloc (DEF_fundef($1)) }
  | letbind
    { dloc (DEF_val($1)) }
  | val_spec
    { dloc (DEF_spec($1)) }
  | default_typ
    { dloc (DEF_default($1)) }
  | Overload id Lsquare enum_body Rsquare
    { dloc (DEF_overload($2,$4)) }
  | Register typ id
    { dloc (DEF_reg_dec(DEC_aux(DEC_reg($2,$3),loc ()))) }
  | Register Alias id Eq exp
    { dloc (DEF_reg_dec(DEC_aux(DEC_alias($3,$5),loc ()))) }
  | Register Alias typ id Eq exp
    { dloc (DEF_reg_dec(DEC_aux(DEC_typ_alias($3,$4,$6), loc ()))) }
  | Scattered scattered_def
    { dloc (DEF_scattered $2) }
  | Function_ Clause funcl
    { dloc (DEF_scattered (sdloc (SD_scattered_funcl($3)))) }
  | Union tid Member typ id
    { dloc (DEF_scattered (sdloc (SD_scattered_unioncl($2,Tu_aux(Tu_ty_id($4,$5), locn 4 5))))) }
  | Union tid Member id
    { dloc (DEF_scattered (sdloc (SD_scattered_unioncl($2,Tu_aux(Tu_id($4), locn 4 4))))) }
  | End id
    { dloc (DEF_scattered (sdloc (SD_scattered_end($2)))) }
  | End tid
    { dloc (DEF_scattered (sdloc (SD_scattered_end($2)))) }

defs_help:
  | def
    { [$1] }
  | def defs_help
    { $1::$2 }

defs:
  | defs_help
    { (Defs $1) }

file:
  | defs Eof
    { $1 }

nonempty_exp_list:
  | semi_exps_help Eof { $1 }
