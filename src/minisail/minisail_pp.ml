open PPrintEngine
open PPrintCombinators

open Minisail_isa.Syntax
module A =  Minisail_isa.Arith 

let rec nat_to_int = function
    A.Zero_nat -> 0
  | A.Suc n -> ((nat_to_int n) + 1)
   
let pp_x = function
    Abs_x (Atom (_, n)) -> string "x" ^^ (string (string_of_int (nat_to_int  n)))

let pp_id x = string (Minisail_isa.Stringa.implode x)

let rec pp_b = function
    B_int -> string "int"
  | B_unit -> string "unit"
  | B_bool -> string "bool"
  | B_bitvec -> string "bits"
  | B_pair (b1,b2) -> string "<" ^^ pp_b b1 ^^ string "," ^^ pp_b b2 ^^ string ">"
  | B_id tyid -> pp_id tyid

let cint = function
  A.Zero_int -> 0
| Pos num ->  (nat_to_int (A.nat_of_num num))
| Neg num -> -1 * (nat_to_int (A.nat_of_num num))
                         
let pp_l = function
  | L_true -> string "T"
  | L_false -> string "F"
  | L_unit -> string "()"
  | L_num n -> string (string_of_int (cint n))
  | L_bitvec bs -> string ("0b" ^ (String.concat "" (List.map (function BitOne -> "1" | BitZero -> "0") bs)))

             
let rec pp_v = function
    V_var x -> pp_x x
  | V_lit l -> pp_l l
  | V_pair (v1,v2) -> string "(" ^^ pp_v v1 ^^ string "," ^^ pp_v v2 ^^ string ")"
  | V_cons (tyid, dc,v) -> pp_id tyid ^^ string "." ^^ pp_id dc ^^ string " " ^^ pp_v v
  | V_consp (tyid,dc,b,v) -> pp_id tyid ^^ string "." ^^ pp_id dc ^^ string " [" ^^ pp_b b ^^ string "] " ^^ pp_v v



let pp_op = function
    Plus -> string "+"
  | LEq -> string "<="


         
let pp_e = function
    AE_val v -> pp_v v
  | AE_fst v -> string "#1 " ^^ pp_v v
  | AE_snd v -> string "#2 " ^^ pp_v v
  | AE_app (f,v) -> pp_id f ^^ string "(" ^^ pp_v v ^^ string ")"
  | AE_appP (f,b,v) -> pp_id f ^^ string "[" ^^ pp_b b ^^ string "] (" ^^ pp_v v ^^ string ")"
  | AE_len v -> string "len " ^^ pp_v v
  | AE_concat (v1,v2) -> pp_v v1 ^^ string "@@" ^^ pp_v v2                       
  | AE_op (opp,v1,v2) -> pp_v v1 ^^ pp_op opp  ^^ pp_v v2
  | AE_split (v1,v2) -> string "split "  ^^ pp_v  v1 ^^ string " " ^^ pp_v v2
  | AE_mvar u -> string "mvar"
               
let rec pp_s = function
    AS_val v -> pp_v v
  | AS_let (x, e, s) -> string "let " ^^ (pp_x x) ^^ string " = " ^^ (pp_e e) ^^ string " in" ^^ hardline ^^ (pp_s s)
  | AS_if(e,s1,s2) -> string "if " ^^ pp_v e ^^
                        string " then {" ^^ (nest 4 (hardline ^^ pp_s s1)) ^^ hardline ^^
                        string "} else {" ^^ (nest 4 (hardline ^^ pp_s s2) ^^ hardline ^^ string "}") 
  | AS_seq (s1,s2) -> pp_s s1 ^^ string ";" ^^ hardline ^^ pp_s s2
  | AS_match (v,bs) -> string "match " ^^ pp_v v ^^ string "{" ^^ nest 4 (hardline ^^ pp_bs bs) ^^ string "}"
  | AS_assign (u,v) -> string "mvar =" ^^ pp_v v                     
and pp_bs = function
    AS_final b -> pp_br b
  | AS_cons (b,bs) -> pp_br b ^^ hardline ^^ string "|" ^^ pp_bs bs
and pp_br = function
    AS_branch (dc,x,s) -> pp_id dc ^^ string " " ^^ pp_x x ^^ string " => " ^^ pp_s s
                     

let pp_tdef = function
    _ -> string "tdef"

let rec pp_ce = function
  | CE_val v -> pp_v v
  | CE_op (op,ce1,ce2) -> pp_ce ce1 ^^ string " op " ^^ pp_ce ce2
  | CE_len v -> string "len " ^^ pp_ce v
  | CE_fst v -> string "#1 " ^^ pp_ce v
  | CE_snd v -> string "#2 " ^^ pp_ce v
            
let rec pp_c = function
    C_true -> string "T"
  | C_false -> string "F"
  | C_eq (e1,e2) -> pp_ce e1 ^^ string " = " ^^ pp_ce e2
  | C_conj (c1,c2) -> pp_c c1 ^^ string " AND " ^^ pp_c c2
  | C_not c -> string "~" ^^ pp_c c
  | C_disj (c1, c2) -> pp_c c1 ^^ string " OR " ^^ pp_c c2
  | C_imp (c1, c2) -> pp_c c1 ^^ string " => " ^^ pp_c c2
            
let pp_t = function
    T_refined_type (z,b,c) -> string "{ " ^^ (pp_x z) ^^ string ":" ^^ pp_b b ^^ string "|" ^^ pp_c c ^^ string "}"
            
let pp_fdef = function
    AF_fundef (f ,(AF_fun_typ_none (AF_fun_typ (x,b,c,t,s)))) ->
    string "function  " ^^ pp_id f ^^ string " :: " ^^  (pp_x x) ^^ string ":" ^^ (pp_b b) ^^ string "[" ^^ pp_c c ^^ string " ] -> " ^^ (pp_t t) ^^ string " =" 
    ^^ (nest 4 (hardline ^^ pp_s s))

let pp_tdef = function
    AF_typedef (tyid,dclist) -> string "union " ^^ string (Minisail_isa.Stringa.implode tyid) ^^
                                string " {" ^^ nest 4 (hardline ^^ 
                                  separate (string "," ^^ hardline) (List.map  (function (ctor,t) -> string (Minisail_isa.Stringa.implode ctor) ^^ string " : " ^^ pp_t t)
                                                           dclist)) ^^ hardline ^^
                                    string "}"
                                                                                                      
    
