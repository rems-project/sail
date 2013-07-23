/**************************************************************************/
/*                        Lem                                             */
/*                                                                        */
/*          Dominic Mulligan, University of Cambridge                     */
/*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            */
/*          Gabriel Kerneis, University of Cambridge                      */
/*          Kathy Gray, University of Cambridge                           */
/*          Peter Boehm, University of Cambridge (while working on Lem)   */
/*          Peter Sewell, University of Cambridge                         */
/*          Scott Owens, University of Kent                               */
/*          Thomas Tuerk, University of Cambridge                         */
/*                                                                        */
/*  The Lem sources are copyright 2010-2013                               */
/*  by the UK authors above and Institut National de Recherche en         */
/*  Informatique et en Automatique (INRIA).                               */
/*                                                                        */
/*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   */
/*  are distributed under the license below.  The former are distributed  */
/*  under the LGPLv2, as in the LICENSE file.                             */
/*                                                                        */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*  notice, this list of conditions and the following disclaimer.         */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*  notice, this list of conditions and the following disclaimer in the   */
/*  documentation and/or other materials provided with the distribution.  */
/*  3. The names of the authors may not be used to endorse or promote     */
/*  products derived from this software without specific prior written    */
/*  permission.                                                           */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    */
/*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     */
/*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    */
/*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       */
/*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    */
/*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     */
/*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         */
/*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  */
/*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       */
/*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   */
/*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         */
/**************************************************************************/

%{

let r = fun x -> x (* Ulib.Text.of_latin1 *)

open Ast

let loc () = Range(Parsing.symbol_start_pos(),Parsing.symbol_end_pos())
let locn m n = Range(Parsing.rhs_start_pos m,Parsing.rhs_end_pos n)

let ploc p = Pat_l(p,loc ())
let eloc e = Expr_l(e,loc ())
let lbloc lb = Letbind(lb,loc ())

let bkloc k = BK_aux(k,loc ())
let kloc k = K_aux(k,loc ())
let tloc t = ATyp_aux(t,loc ())
let lloc l = L_aux(l,loc ())
let ploc p = P_aux(p,(None,loc ()))
let fploc p = FP_aux(p,(None,loc ()))

let dloc d = DEF_aux(d,loc ())

let pat_to_let p =
  match p with
    | Pat_l(P_app(Id([],v,_),(arg::args as a)),_) ->
        Some((v,a))
    | _ ->
        None

let pat_to_letfun p =
  match p with
    | Pat_l(P_app(Id([],v,_),(arg::args as a)),_) ->
        (v,a)
    | Pat_l(_,l) -> 
        raise (Parse_error_locn(l,"Bad pattern for let binding of a function"))

let build_fexp (Expr_l(e,_)) l =
  match e with
    | Infix(Expr_l(Ident(i), l'),SymX_l((stx,op),l''),e2) when String.compare op (r"=") = 0 ->
        Fexp(i, stx, e2, l)
    | _ ->
        raise (Parse_error_locn(l,"Invalid record field assignment (should be id = exp)"))

let mod_cap n =
  if not (Name.starts_with_upper_letter (Name.strip_lskip (Name.from_x n))) then
    raise (Parse_error_locn(Ast.xl_to_l n, "Module name must begin with an upper-case letter"))
  else
    ()

let space = " "
let star = "*"

(*let mk_pre_x_l sk1 (sk2,id) sk3 l =
  if (sk2 = None || sk2 = Some []) && (sk3 = None || sk3 = Some []) then
    PreX_l(sk1,(None,id),None,l)
  else if (sk2 = Some [Ws space] && 
           sk3 = Some [Ws space] && 
           (Ulib.Text.left id 1 = star ||
            Ulib.Text.right id 1 = star)) then
    PreX_l(sk1,(None,id),None,l)
  else
    raise (Parse_error_locn(l, "illegal whitespace in parenthesised infix name"))*)


%}

/*Terminals with no content*/

%token <Ast.terminal> And As Bits Case Clause Const Default Effect Effects End Enum Else False 
%token <Ast.terminal> Forall Function_ If_ In IN Let_ Member Nat Order Pure Rec Register  
%token <Ast.terminal> Scattered Struct Switch Then True Type TYPE Typedef Union With Val

%token <Ast.terminal> AND Div_ EOR Mod OR Quot Rem 

%token <Ast.terminal> Bar Colon Comma Dot Eof Minus Semi Under
%token <Ast.terminal> Lcurly Rcurly Lparen Rparen Lsquare Rsquare
%token <Ast.terminal> BarBar BarGt BarSquare DotDot MinusGt LtBar SquareBar 

/*Terminals with content*/

%token <Ast.terminal * string> Id
%token <Ast.terminal * int> Num
%token <Ast.terminal * string> String Bin Hex

%token <Ast.terminal * string> Amp At Carrot  Div Eq Excl Gt Lt Plus Star Tilde 
%token <Ast.terminal * string> AmpAmp CarrotCarrot ColonColon ColonEq EqDivEq EqEq ExclEq ExclExcl  
%token <Ast.terminal * string> GtEq GtEqPlus GtGt GtGtGt GtPlus HashGtGt HashLtLt   
%token <Ast.terminal * string> LtEq LtEqPlus LtGt LtLt LtLtLt LtPlus StarStar TildeCarrot

%token <Ast.terminal * string> GtEqUnderS GtEqUnderSi GtEqUnderU GtEqUnderUi GtGtUnderU GtUnderS 
%token <Ast.terminal * string> GtUnderSi GtUnderU GtUnderUi LtEqUnderS LtEqUnderSi LtEqUnderU 
%token <Ast.terminal * string> LtEqUnderUi LtUnderS LtUnderSi LtUnderU LtUnderUi StarUnderS 
%token <Ast.terminal * string> StarUnderSi StarUnderU StarUnderUi TwoCarrot

%token <Ast.terminal * string> AmpI AtI CarrotI  DivI EqI ExclI GtI LtI PlusI StarI TildeI
%token <Ast.terminal * string> AmpAmpI CarrotCarrotI ColonColonI ColonEqI EqDivEqI EqEqI ExclEqI ExclExclI  
%token <Ast.terminal * string> GtEqI GtEqPlusI GtGtI GtGtGtI GtPlusI HashGtGtI HashLtLtI  
%token <Ast.terminal * string> LtEqI LtEqPlusI LtGtI LtLtI LtLtLtI LtPlusI StarStarI TildeCarrotI

%token <Ast.terminal * string> GtEqUnderSI GtEqUnderSiI GtEqUnderUI GtEqUnderUiI GtGtUnderUI GtUnderSI 
%token <Ast.terminal * string> GtUnderSiI GtUnderUI GtUnderUiI LtEqUnderSI LtEqUnderSiI LtEqUnderUI 
%token <Ast.terminal * string> LtEqUnderUiI LtUnderSI LtUnderSiI LtUnderUI LtUnderUiI StarUnderSI 
%token <Ast.terminal * string> StarUnderSiI StarUnderUI StarUnderUiI TwoCarrotI

%start file
%type <Ast.defs> defs
%type <Ast.typ> typ
%type <Ast.pat> pat
%type <Ast.exp> exp
%type <Ast.defs * Ast.terminal> file


%%

id:
  | Id
    { X_l($1, loc ()) }
  | Lparen Eq Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen IN Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen AmpAmp Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen BarBar Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen ColonColon Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen Star Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen Plus Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen GtEq Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }
  | Lparen At Rparen
    { mk_pre_x_l $1 $2 $3 (loc ()) }

atomic_kind:
  | TYPE
    { bkloc (BK_type($1)) }
  | Nat
    { bkloc (BK_nat($1)) }
  | Order
    { bkloc (BK_order($1)) }
  | Effects
    { bkloc (BK_effects($1)) }

kind:
  | atomic_kind
    { [ ($1,None) ] }
  | atomic_kind MinusGt kind
    { ($1,$2)::$3 }

effect:
  | id
    { (match id with
       | Id_aux(Id(s,t),l) ->
	 Effect_aux
	   ((match s with
	   | "rreg" -> (Effect_rreg t)
	   | "wreg" -> (Effect_wreg t)
	   | "rmem" -> (Effect_rmem t)
	   | "wmem" -> (Effect_wmem t)
	   | "undef" -> (Effect_undef t)
	   | "unspec" -> (Effect_unspec t)
	   | "nondet" -> (Effect_nondet t)
	   | _ -> Parse_error_locn(l, "Invalid effect")),l)
       | _ -> Parse_error_locn(loc () , "Invalid effect")) }

effect_list:
  | effect
    { [($1,None)] }
  | effect Comma effect_list
    { ($1,Some($2))::$3 }

effect_typ:
  | Effect id
    { tloc (ATyp_efid($1,$2)) }
  | Effect Lcurly effect_list Rcurly
    { tloc (ATyp_effects($1,$2,$3,$4)) }
  | Pure
    { tloc (ATyp_effects($1,[],None)) }

atomic_typ:
  | id
    { tloc (ATyp_var $1) }
  | Num
    { tloc (ATyp_constant(fst $1, snd$1)) }
  | Under
    { tloc (ATyp_wild($1)) }
  | effect_typ
    { $1 }
  | Lparen typ Rparen
    { $2 }

atomic_typs:
  | atomic_typ
    { [$1] }
  | atomic_typ atomic_typs
    { $1::$2 }

app_typ:
  | atomic_typ
    { $1 }
  | id atomic_typs
    { tloc (ATyp_app($1,$2)) }

star_typ_list:
  | app_typ
    { [($1,None)] }
  | app_typ Star star_typ_list
    { ($1,fst $2)::$3 }

star_typ:
  | star_typ_list
    { match $1 with
        | [] -> assert false
        | [(t,None)] -> t
        | [(t,Some _)] -> assert false
        | ts -> tloc (ATyp_tup(ts)) }

exp_typ:
   | star_typ
     { $1 }
   | Num StarStar typ
     { if (2 = (fst $1))
       then tloc (ATyp_exp((fst $1,snd $1),$2,$3))
       else Parse_error_locn(loc (), "Only 2 is a valid exponent base in Nats") }

nexp_typ:
   | exp_typ
     { $1 }
   | atomic_typ Plus typ
     { tloc (ATyp_sum($1,fst $2,$3)) }

typ:
  | nexp_typ
    { $1 }
  | star_typ MinusGt atomic_typ effect_typ
    { tloc (ATyp_fn($1,$2,$3,$4)) }

lit:
  | True
    { lloc (L_true($1)) }
  | False
    { lloc (L_false($1)) }
  | Num
    { lloc (L_num(fst $1, snd $1)) }
  | String
    { lloc (L_string(fst $1, snd $1)) }
  | Lparen Rparen
    { lloc (L_unit($1,$2)) }
  | Bin
    { lloc (L_bin(fst $1, snd $1)) }
  | Hex
    { lloc (L_hex(fst $1, snd $1)) }


atomic_pat:
  | lit
    { ploc (P_lit($1)) }
  | Under
    { ploc (P_wild($1)) }
  | Lparen pat As id Rparen
    { ploc (P_as($1,$2,$3,$4,$5)) }
/* Because of ( id id ) being either application or type casts, this is inherently ambiguous */
/*  | Lparen atomic_typ pat Rparen
    { ploc (P_typ($1,$2,$3,$4)) } */
  | id
    { ploc (P_app($1,[])) } 
  | Lcurly fpats Rcurly
    { ploc (P_record($1,fst $2,fst (snd $2),snd (snd $2),$3)) }
  | Lsquare pat Rsquare
    { ploc (P_vector($1,[($2,None)],$3)) }
  | Lsquare comma_pats Rsquare
    { ploc (P_vector($1,$2,$3)) }
  | Lsquare npats Rsquare
    { ploc (P_vector_indexed($1,$2,$3)) } 
  | Lparen comma_pats Rparen
    { ploc (P_tup($1,$2,$3)) } 
  | SquareBar comma_pats BarSquare
    { ploc (P_list($1,$2,$3)) } 
  | Lparen pat Rparen
    { $2 }


atomic_pats:
  | atomic_pat
    { [$1] }
  | atomic_pat atomic_pats
    { $1::$2 }

app_pat:
  | atomic_pat
    { $1 }
  | id atomic_pats
    { ploc (P_app($1,$2)) }

pat_colons:
  | atomic_pat Colon atomic_pat
    { ([($1,$2);($3,None)]) }
  | atomic_pat Colon pat_colons
    { (($1,$2)::$3) }

pat:
  | app_pat
    { $1 }
  | pat_colons
    { ploc (P_vector_concat($1)) } 

comma_pats:
  | atomic_pat Comma atomic_pat
    { [($1,$2);($3,None)] }
  | atomic_pat Comma comma_pats
    { ($1,$2)::$3 }

fpat:
  | id Eq pat
    { fploc (FP_Fpat($1,fst $2,$3)) }

fpats:
  | fpat
    { ([($1,None)], (None,false)) }
  | fpat Semi
    { ([($1,None)], ($2,true)) }
  | fpat Semi fpats
    { (($1,$2)::fst $3, snd $3) }

npat: 
  | Num Eq pat
    { ($1,fst $2,$3) }

npats:
  | npat
    { ([($1,None)]) }
  | npat Comma npats
    { (($1,$2)::$3) }

atomic_exp:
  | Lcurly semi_exps Rcurly
    { eloc (E_block($1,$2,$3)) }
  | id 
    { eloc (E_id($1)) }
  | lit
    { eloc (E_lit($1)) }
  | Lparen exp Rparen
    { $2 }
/*  | Lparen typ Rparen exp
    { eloc (E_cast($1,$2,$3,$4)) }
*/  | Lparen comma_exps Rparen
    { eloc (E_tup($1,$2,$3)) }
  | Lsquare comma_exps Rsquare
    { eloc (E_vector($1,$2,$3)) }
  | Lsquare exp With exp Eq exp Rsquare
    { eloc (E_vector_update($1,$2,$3,$4,fst $5,$6,$7)) }
  | Lsquare exp With exp Colon exp Eq exp Rsquare
    { eloc (E_vector_subrance($1,$2,$3,$4,$5,fst $6,$7,$8)) }
  | SquareBar comma_exps BarSquare
    { eloc (E_list($1,$2,$3)) }
  | Switch exp Lcurly case_exps Rcurly
    { eloc (E_case($1,$2,$3,$4,$5)) }


field_exp:
  | atomic_exp
    { $1 }
  | atomic_exp Dot id
    { eloc (E_field($1,$2,$3)) }

vaccess_exp:
  | field_exp
    { $1 }
  | atomic_exp Lsquare exp Rsquare
    { eloc (E_vector_access($1,$2,$3,$4)) }
  | atomic_exp Lsquare exp DotDot exp Rsquare
    { eloc (E_vector_subrange($1,$2,$3,$4,$5,$6)) }

app_exp:
  | vaccess_exp
    { $1 }
  | atomic_exp exps
    { eloc (E_app($1,$2)) }

exps:
  | atomic_exp
    { [$1] }
  | atomic_exp exps
    { $1::$2 }

right_atomic_exp:
  | If_ exp Then exp Else exp
    { eloc (E_if($1,$2,$3,$4,$5,$6)) }
  | letbind In exp
    { eloc (E_let($1,$2,$3)) } 

starstar_exp:
  | app_exp
    { $1 }
  | starstar_exp StarStar app_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


starstar_right_atomic_exp:
  | right_atomic_exp
    { $1 }
  | starstar_exp StarStar right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


star_exp:
  | starstar_exp
    { $1 }
  | star_exp Star starstar_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


star_right_atomic_exp:
  | starstar_right_atomic_exp
    { $1 }
  | star_exp Star starstar_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

plus_exp:
  | star_exp
    { $1 }
  | plus_exp Plus star_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


plus_right_atomic_exp:
  | star_right_atomic_exp
    { $1 }
  | plus_exp Plus star_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

cons_exp:
  | plus_exp
    { $1 }
  | plus_exp ColonColon cons_exp
    { eloc (E_cons($1,fst $2,$3)) }


cons_right_atomic_exp:
  | plus_right_atomic_exp
    { $1 }
  | plus_exp ColonColon cons_right_atomic_exp
    { eloc (E_cons($1,fst $2,$3)) }

at_exp:
  | cons_exp
    { $1 }
  | cons_exp At at_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


at_right_atomic_exp:
  | cons_right_atomic_exp
    { $1 }
  | cons_exp At at_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

eq_exp:
  | at_exp
    { $1 }
  | eq_exp Eq at_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp GtEq at_exp
    { eloc (E_app_infix ($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp IN at_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp ColonEq at_exp
    { eloc (E_assign($1,$2,$3)) }


eq_right_atomic_exp:
  | at_right_atomic_exp
    { $1 }
  | eq_exp Eq at_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

and_exp:
  | eq_exp
    { $1 }
  | eq_exp AmpAmp and_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


and_right_atomic_exp:
  | eq_right_atomic_exp
    { $1 }
  | eq_exp AmpAmp and_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

or_exp:
  | and_exp
    { $1 }
  | and_exp BarBar or_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }


or_right_atomic_exp:
  | and_right_atomic_exp
    { $1 }
  | and_exp BarBar or_right_atomic_exp
    { eloc (E_app_infix($1,SymX_l($2, locn 2 2), $3)) }

exp:
  | app_exp
    { $1 } 
  | right_atomic_exp
    { $1 }

comma_exps:
  | exp Comma exp
    { [($1,$2);($3,None)] }
  | exp Comma comma_exps
    { ($1,$2)::$3 }
 
semi_exps_help:
  | exp
    { ([($1,None)], (None,false)) }
  | exp Semi
    { ([($1,None)], ($2,true)) }
  | exp Semi semi_exps_help
    { (($1,$2)::fst $3, snd $3) }

semi_exps:
  |
    { ([], (None, false)) }
  | semi_exps_help
    { $1 }

case_exp:
  | Case patsexp
    { ($1,$2) }

case_exps:
  | case_exp
    { [$1] }
  | case_exp case_exps
    { $1::$2 }

patsexp:
  | atomic_pats1 MinusGt exp
    { Patsexp($1,$2,$3,loc ()) }

atomic_pats1:
  | atomic_pat
    { [$1] }
  | atomic_pat atomic_pats1
    { $1::$2 } 

letbind:
  | Let_ atomic_pat Eq exp
    { }
  | typquant atomic_typ atomic_pat Eq exp
    { }
  | Let_ atomic_typ atomic_pat Eq exp
    { }

funcl: 
  | id atomic_pats1 Eq exp
    { reclloc (FCL_Funcl($1,$2,fst $3,$4)) }

funcl_ands:
  | funcl
    { [$1] }
  | funcl And funcl_ands
    { $1::$3 }


fun_def:
  | Function_ Rec typquant typ effect_typ funcl_ands
    { $1,$2,$3,$4,$5 }
  | Function_ Rec typquant typ effect_typ funcl_ands
    { }
  | Function_ Rec typ funcl_ands
    { $1,$2,$3,$4 }
  | Function_ Rec funcl_ands
    { $1,$2,$3 }
  | Function_ typquant typ effect_typ funcl_ands
    { $1,$2,$3,$4 }
  | Function_ typquant typ funcl_ands
    { $1,$2,$3 }
  | Function_ typ funcl_ands
    { $1,$2,$3 }
  | Function_ funcl_ands
    { $1,$2 }


val_spec:
  | Val typschm id
    { Val_spec($1,$2,$3) }

texp:
  | typ
    { Te_abbrev($1) }

kinded_id:
  | id
    { }
  | kind id
    { }
  | Lparen kinded_id Rparen
    { }

kinded_ids:
  | kinded_id
    { [$1] }
  | kinded_id kinded_ids
    { $1::$2 }

nums:
  | Num
    { [($1,None)] }
  | Num Comma nums
    { ($1,$2)::$3 }

nexp_constraint:
  | typ Eq typ
    { NC_aux(NC_fixed($1,(fst $2),$3), loc () ) }
  | typ GtEq typ
    { NC_aux(NC_bounded_ge($1,(fst $2),$3), loc () ) }
  | typ LtEq typ
    { NC_aux(NC_bounded_le($1,(fst $2),$3), loc () ) }
  | id IN Lcurly nums Rcurly
    { NC_aux(NC_nat_set_bounded($1,$2,$3,$4,$5)) } 
    
nexp_constraints:
  | nexp_constraint
    { [($1,None)] }
  | nexp_constraint Comma nexp_constraints 
    { ($1,$2)::$3 }

typquant:
  | Forall kinded_ids Amp nexp_constraints Dot
    { typql(TypQ_tq($1,$2,$3,$4,$5)) }
  | Forall kinded_ids Dot
    { typql(TypQ_no_constraint($1,$2,$3)) }

typschm:
  | typquant typ
    { TypS($1,$2) }
  | typ
    { TypS(None,$1) }

name_sect:
  | Lsquare id Eq String Rsquare
    { Name_sect_some($1,$2,fst $3,(fst $4),(snd $4),$5) }

c_def_body:
  | typ id
    { [(($1,$2),None)] }
  | typ id Semi
    { [(($1,$2),Some)] }
  | typ id Semi c_def_body
    { (($1,$2)$3)::$4 }

index_range_atomic:
  | Num
    { IR_Num($1) }
  | Num DotDot Num
    { IR_Range($1,$2,$3) }
  | Lparen index_range Rparen
    { $2 }

index_range:
  | index_range_atomic
    { $1 }
  | index_range_atomic Comma index_range
    { IR_concat($1,$2,$3) } 

r_def_body:
  | index_range
    { [(1,None)] }
  | index_range Semi
    { [$1,$2] }
  | index_range Semi r_def_body
    { ($1,$2)::$3 }


type_def:
  | Typedef id name_sect Eq typschm
    {}
  | Typedef id Eq typschm
    { }
  | Typedef id name_sect Eq Const Struct typquant Lcurly c_def_body Rcurly
    {}
  | Typedef id Eq Const Struct typquant Lcurly c_def_body Rcurly
    {}
  | Typedef id name_sect Eq Const Struct Lcurly c_def_body Rcurly
    {}
  | Typedef id Eq Const Struct Lcurly c_def_body Rcurly
    {}
  | Typedef id name_sect Eq Const Union typquant Lcurly c_def_body Rcurly
    {}
  | Typedef id Eq Const Union typquant Lcurly c_def_body Rcurly
    {}
  | Typedef id name_sect Eq Const Union Lcurly c_def_body Rcurly
    {}
  | Typedef id Eq Const Union Lcurly c_def_body Rcurly
    {}
  | Typedef id Eq Register Bits Lsquare typ Colon typ Rsquare Lcurly r_def_body Rcurly
    {}


default_typ:
  | Default atomic_kind id
    { $1,$2,$3 }
  | Default typ id
    { $1,$2,$3 } 

 
scattered_def:
  | Function_ Rec typschm effect_typ id
    { (DEF_scattered_function(None,$1,(Rec_rec ($2)),$3,$4,$5)) }
  | Function_ Rec typschm id
    { (DEF_scattered_function(None,$1,(Rec_rec ($2)),$3,$4)) }
  | Function_ Rec id
    { DEF_scattered_function(None,$1,$2,None,None,$3) }
  | Function_ typschm effect_typ id
    { (DEF_scattered_function(None,$1,(Rec_rec ()),$2,$3,$4)) }
  | Function_ typschm id
    { (DEF_scattered_function(None,$1,(Rec_rec ($2)),$3,)) }
  | Function_ id
    { DEF_scattered_function(None,$1,$2,None,None,) }
  | Typedef id name_sect Eq Const Union typquant
    { dloc (DEF_scattered_variant(None,$1,$2,$3,$4,$5,$6,$7)) }
  | Typedef id Eq Const Union typquant
    { dloc (DEF_scattered_variant(None,$1,Name_sect_none,$2,$3,$4,$5,$6)) }
  | Typedef id name_sect Eq Const Union
    { dloc (DEF_scattered_variant(None,$1,$2,$3,$4,$5,$6,None)) }
  | Typedef id Eq Const Union
    { dloc (DEF_scattered_variant(None,$1,Name_sect_none,$2,$3,$4,$5,None)) }

def:
  | type_def
    { dloc (DEF_type($1)) }
  | fun_def
    { dloc (DEF_fundef($1)) }
  | letbind
    { dloc (DEF_val($1)) }
  | val_spec
    { dloc (DEF_spec($1)) }
  | default_typ 
    { dloc (DEF_default($1)) }
  | Register typ id
    { dloc (DEF_reg_dec($1,$2,$3)) }
  | Scattered scattered_def
    { dloc (match ($2) with
            | DEF_scattered_function(_,f,r,t,e,i) -> DEF_scattered_function($1,f,r,t,e,i)
            | DEF_scattered_variant(_,t,i,n,e,c,u,ty) -> DEF_scattered_variant($1,t,i,n,e,c,u,ty)) }
  | Function_ Clause funcl
    { dloc (DEF_funcl($1,$2,$3)) }
  | Union id Member typ id
    { dloc (DEF_scattered_unioncl($1,$2,$3,$4,$5)) }
  | End id 
    { dloc (DEF_scattered_end($1,$2)) }

defs_help:
  | def
    { [$1] }
  | def defs_help
    { $1::$2 }

defs:
  | defs_help
    { Defs($1) }

file:
  | defs Eof
    { ($1,$2) }

