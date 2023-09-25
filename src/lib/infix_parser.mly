
%{

[@@@coverage exclude_file]

module Big_int = Nat_big_num
open Parse_ast

let loc n m = Range (n, m)

let mk_id id n m = Id_aux (id, loc n m)
let mk_typ t n m = ATyp_aux (t, loc n m)
let mk_exp e n m = E_aux (e, loc n m)

let deinfix = function
  | (Id_aux (Id v, l)) -> Id_aux (Operator v, l)
  | (Id_aux (Operator v, l)) -> Id_aux (Id v, l)

type lchain =
  LC_lt
| LC_lteq
| LC_nexp of atyp

let tyop op t1 t2 s e = mk_typ (ATyp_app (Id_aux (Operator op, loc s e), [t1; t2])) s e

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

%token Eof

%token <Parse_ast.exp> Exp
%token <Parse_ast.atyp> Typ

%token <Parse_ast.id> Op0 Op1 Op2 Op3 Op4 Op5 Op6 Op7 Op8 Op9
%token <Parse_ast.id> Op0l Op1l Op2l Op3l Op4l Op5l Op6l Op7l Op8l Op9l
%token <Parse_ast.id> Op0r Op1r Op2r Op3r Op4r Op5r Op6r Op7r Op8r Op9r

%token Lt Gt LtEq GtEq Minus Star Plus ColonColon At In
%token TwoCaret

%start typ_eof
%start exp_eof
%type <Parse_ast.atyp> typ_eof
%type <Parse_ast.exp> exp_eof

%%

typ_eof:
  | t = typ0; Eof
    { t }

typ0:
  | typ1 Op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ0l Op0l typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 Op0r typ0r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }
typ0l:
  | typ1 Op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ0l Op0l typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }
typ0r:
  | typ1 Op0 typ1 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 Op0r typ0r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1 { $1 }

typ1:
  | typ2 Op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1l Op1l typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 Op1r typ1r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }
typ1l:
  | typ2 Op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ1l Op1l typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }
typ1r:
  | typ2 Op1 typ2 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 Op1r typ1r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2 { $1 }

typ2:
  | typ3 Op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2l Op2l typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 Op2r typ2r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 { $1 }
typ2l:
  | typ3 Op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ2l Op2l typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 { $1 }
typ2r:
  | typ3 Op2 typ3 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 Op2r typ2r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3 { $1 }

typ3:
  | typ4 Op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3l Op3l typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 Op3r typ3r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 { $1 }
typ3l:
  | typ4 Op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ3l Op3l typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 { $1 }
typ3r:
  | typ4 Op3 typ4 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 Op3r typ3r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4 { $1 }

typ4:
  | typ5 Op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4l Op4l typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 Op4r typ4r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | lchain { desugar_lchain $1 $startpos $endpos }
  | rchain { desugar_rchain $1 $startpos $endpos }
  | typ5 { $1 }
typ4l:
  | typ5 Op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ4l Op4l typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 { $1 }
typ4r:
  | typ5 Op4 typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 Op4r typ4r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5 { $1 }

typ5:
  | typ6 Op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5l Op5l typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 Op5r typ5r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }
typ5l:
  | typ6 Op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ5l Op5l typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }
typ5r:
  | typ6 Op5 typ6 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 Op5r typ5 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6 { $1 }

typ6:
  | typ7 Op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Op6l typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 Op6r typ6r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Plus typ7 { mk_typ (ATyp_sum ($1, $3)) $startpos $endpos }
  | typ6l Minus typ7 { mk_typ (ATyp_minus ($1, $3)) $startpos $endpos }
  | typ7 { $1 }
typ6l:
  | typ7 Op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Op6l typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ6l Plus typ7 { mk_typ (ATyp_sum ($1, $3)) $startpos $endpos }
  | typ6l Minus typ7 { mk_typ (ATyp_minus ($1, $3)) $startpos $endpos }
  | typ7 { $1 }
typ6r:
  | typ7 Op6 typ7 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 Op6r typ6r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7 { $1 }

typ7:
  | typ8 Op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Op7l typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 Op7r typ7r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Star typ8 { mk_typ (ATyp_times ($1, $3)) $startpos $endpos }
  | typ8 { $1 }
typ7l:
  | typ8 Op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Op7l typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ7l Star typ8 { mk_typ (ATyp_times ($1, $3)) $startpos $endpos }
  | typ8 { $1 }
typ7r:
  | typ8 Op7 typ8 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 Op7r typ7r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8 { $1 }

typ8:
  | typ9 Op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8l Op8l typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9 Op8r typ8r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }
typ8l:
  | typ9 Op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ8l Op8l typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }
typ8r:
  | typ9 Op8 typ9 { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9 Op8r typ8r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | TwoCaret typ9 { mk_typ (ATyp_exp $2) $startpos $endpos }
  | Minus typ9 { mk_typ (ATyp_neg $2) $startpos $endpos}
  | typ9 { $1 }

typ9:
  | atomic_typ In atomic_typ { mk_typ (ATyp_in ($1, $3)) $startpos $endpos }
  | atomic_typ Op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9l Op9l atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ Op9r typ9r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }
typ9l:
  | atomic_typ Op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | typ9l Op9l atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }
typ9r:
  | atomic_typ Op9 atomic_typ { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ Op9r typ9r { mk_typ (ATyp_app (deinfix $2, [$1; $3])) $startpos $endpos }
  | atomic_typ { $1 }

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

atomic_typ:
  | Typ
    { $1 }

exp_eof:
  | exp0 Eof
    { $1 }

exp0:
  | exp1 Op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp0l Op0l exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 Op0r exp0r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }
exp0l:
  | exp1 Op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp0l Op0l exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }
exp0r:
  | exp1 Op0 exp1 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 Op0r exp0r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1 { $1 }

exp1:
  | exp2 Op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1l Op1l exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 Op1r exp1r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }
exp1l:
  | exp2 Op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp1l Op1l exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }
exp1r:
  | exp2 Op1 exp2 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 Op1r exp1r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2 { $1 }

exp2:
  | exp3 Op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2l Op2l exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 Op2r exp2r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 { $1 }
exp2l:
  | exp3 Op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp2l Op2l exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 { $1 }
exp2r:
  | exp3 Op2 exp3 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 Op2r exp2r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3 { $1 }

exp3:
  | exp4 Op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3l Op3l exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 Op3r exp3r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 { $1 }
exp3l:
  | exp4 Op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp3l Op3l exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 { $1 }
exp3r:
  | exp4 Op3 exp4 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 Op3r exp3r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4 { $1 }

exp4:
  | exp5 Op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 Lt exp5 { mk_exp (E_app_infix ($1, mk_id (Id "<") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 Gt exp5 { mk_exp (E_app_infix ($1, mk_id (Id ">") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 LtEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id "<=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp5 GtEq exp5 { mk_exp (E_app_infix ($1, mk_id (Id ">=") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp4l Op4l exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 Op4r exp4r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }
exp4l:
  | exp5 Op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp4l Op4l exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }
exp4r:
  | exp5 Op4 exp5 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 Op4r exp4r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5 { $1 }

exp5:
  | exp6 Op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5l Op5l exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 Op5r exp5r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 At exp5r { mk_exp (E_vector_append ($1, $3)) $startpos $endpos }
  | exp6 ColonColon exp5r { mk_exp (E_cons ($1, $3)) $startpos $endpos }
  | exp6 { $1 }
exp5l:
  | exp6 Op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp5l Op5l exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 { $1 }
exp5r:
  | exp6 Op5 exp6 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 Op5r exp5r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6 At exp5r { mk_exp (E_vector_append ($1, $3)) $startpos $endpos }
  | exp6 ColonColon exp5r { mk_exp (E_cons ($1, $3)) $startpos $endpos }
  | exp6 { $1 }

exp6:
  | exp7 Op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Op6l exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 Op6r exp6r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Plus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "+") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp6l Minus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "-") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp7 { $1 }
exp6l:
  | exp7 Op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Op6l exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp6l Plus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "+") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp6l Minus exp7 { mk_exp (E_app_infix ($1, mk_id (Id "-") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp7 { $1 }
exp6r:
  | exp7 Op6 exp7 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 Op6r exp6r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7 { $1 }

exp7:
  | exp8 Op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Op7l exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 Op7r exp7r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Star exp8 { mk_exp (E_app_infix ($1, mk_id (Id "*") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp8 { $1 }
exp7l:
  | exp8 Op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Op7l exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp7l Star exp8 { mk_exp (E_app_infix ($1, mk_id (Id "*") $startpos($2) $endpos($2), $3)) $startpos $endpos }
  | exp8 { $1 }
exp7r:
  | exp8 Op7 exp8 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 Op7r exp7r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8 { $1 }

exp8:
  | exp9 Op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8l Op8l exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 Op8r exp8r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }
exp8l:
  | exp9 Op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp8l Op8l exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }
exp8r:
  | exp9 Op8 exp9 { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9 Op8r exp8r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | TwoCaret exp9 { mk_exp (E_app (mk_id (Id "pow2") $startpos($1) $endpos($1), [$2])) $startpos $endpos }
  | exp9 { $1 }

exp9:
  | atomic_exp Op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9l Op9l atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp Op9r exp9r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }
exp9l:
  | atomic_exp Op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | exp9l Op9l atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }
exp9r:
  | atomic_exp Op9 atomic_exp { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp Op9r exp9r { mk_exp (E_app_infix ($1, $2, $3)) $startpos $endpos }
  | atomic_exp { $1 }

atomic_exp:
  | Star atomic_exp { mk_exp (E_deref $2) $startpos $endpos }
  | Exp
    { $1 }
