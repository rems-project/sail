(*
   Convert Sail type to MiniSail type. Sail types include type level variables for kinds
   Int, Bool, Order and Type. MiniSail types do not include type level variables apart from types.
*)

open PPrintEngine
open PPrintCombinators

module A = Ast 
module P = Parse_ast
open Util_ms
       
open Minisailplus_ast.SyntaxVCT  (* Mini Sail AST as obtain from Isabelle *)
open Minisailplus_ast.SyntaxPED  (* Mini Sail AST as obtain from Isabelle *)
open Minisailplus_ast.Location
open Minisailplus_ast.Contexts
open Minisailplus_core.ConvertTypes
open Minisailplus_pp

module KBindings = Map.Make(String)
module KABindings = Map.Make(String)
module TBindings = Map.Make(String)
module FBindings = Map.Make(String)
module SBindings = Map.Make(String)
module ESet = Set.Make(String)

module TEnv = Map.Make(String)
module VariantEnv = Map.Make(String)

type mods = ((cep*cep) list)
type ceks =  (string option*cep) list
type xbcs = ((xp* (bp*cp)) list)
              
type ctx_type = CtxType of (xbcs  * tau * mods * ceks )
type ctx_kind = CtxKind of (xbcs * cep * mods * ceks )

exception InvertFail
                            
type 'a ctx = {
    kinds : A.kind KBindings.t;
    kind_abbrev : ctx_kind KABindings.t;
    types : ctx_type  TBindings.t;
    funs : ( ((xp* (bp*cp)) list) *  bp * cp * tau) FBindings.t;
    scattereds : (tau * ( ( ('a A.pat)* ('a A.exp)) list)) SBindings.t;
    ended : ESet.t;
    mvars : ESet.t;
  }

let initial_ctx = {
    kinds = KBindings.empty;
    kind_abbrev = KABindings.empty;
    types = TBindings.empty;
    funs = FBindings.empty;
    scattereds = SBindings.empty;
    ended = ESet.empty;
    mvars = ESet.empty;
  }

let pp_location l = match l with
  | P.Unknown -> "Unknown "
  (*  | Int (s, _) -> "Somewhere " ^ s*)
  | P.Generated _ -> "Generated "
  | P.Range (p1,p2) -> "Range " ^ p1.pos_fname ^ " " ^ string_of_int(p1.pos_lnum) ^ ":" ^ string_of_int(p1.pos_cnum-p1.pos_bol) ^ " - " 
                     ^ string_of_int(p2.pos_lnum) ^ ":" ^ string_of_int(p2.pos_cnum-p2.pos_bol)

let b_of (T_refined_type (_,b,_)) = b
let c_of (T_refined_type (_,_,c)) = c

let zvar = VIndex
let xvar = VNamed "#x"

let c_le v1 v2 = C_eq (CE_val (V_lit (L_true)) , ( CE_bop (LEq, v1, v2)))
let c_ge v1 v2 = C_eq (CE_val (V_lit (L_true)) , ( CE_bop (GEq, v1, v2)))
let c_lt v1 v2 = C_eq (CE_val (V_lit (L_true)) , ( CE_bop (LT, v1, v2)))
let c_gt v1 v2 = C_eq (CE_val (V_lit (L_true)) , ( CE_bop (GT, v1, v2)))
let c_eq v1 v2 = C_eq (v1,v2)
let c_eq_x x1 x2 = C_eq  (CE_val (V_var (x1)), CE_val  (V_var (x2)))

let int_of_int i = (Big_int.big_int_of_string (string_of_int i))
                                    
(* Convert from the Sail parse_ast big num to big_int int *)
let big_int_of_big_num i = Big_int.big_int_of_string (P.Big_int.to_string i)

let convert_to_isa (s : string ) : string = if s = "arg#" then "argg" else s (* FIXPE remove call to this when ok with string type *)
let convert_kid (A.Kid_aux (Var id,_)) = convert_to_isa id

let mk_proj_op len i = convert_to_isa ((string_of_int len) ^ "X" ^ (string_of_int i))

let mk_range_c_ce zvar left right = C_conj (c_le left zvar, c_le zvar right )
                                           
let mk_range_c zvar left right =  mk_range_c_ce  (CE_val (V_var (zvar))) left right

let merge_assoc (xs : ('a * 'b) list ) : (('a * ('b list)) list) =
  let (keys,_) = List.split xs in
  List.map (fun a -> (a,List.map snd (List.filter (fun (a',b) -> a' = a) xs))) (List.sort_uniq (String.compare) keys)
                                         
let convert_num  n = V_lit (L_num  n ) 

let convert_big_num = convert_num

let nat_of_big_num n = (Big_int.big_int_of_string (P.Big_int.to_string n)) (*Arith.Nat (Big_int.big_int_of_int n) *)


let pp_line s = PPrintEngine.ToChannel.compact stderr (s ^^ (string "\n"))

let contains_var ce k = List.mem k (fvs_cep ce)

let convert_order ((A.A_aux (A_order (Ord_aux (ord,_)),_)) : A.typ_arg) : order = match ord with
  | A.Ord_dec -> Ord_dec
  | A.Ord_inc -> Ord_inc
  | _ -> Ord_inc (* FIXPE *)

                                 
(* Extract from the Sail typ its MiniSail base type *)
let rec to_ms_base ctx (A.Typ_aux (typ,loc)) : bp = 
  match typ with
       | A.Typ_id (Id_aux (Id id,loc2)) -> (match id with
            | "int" -> B_int
            | "bool"|"boolean" -> B_bool
            | "reg_size" ->       B_int
            | "unit" ->           B_unit
            | "bit" ->            B_bit
            | "real" ->           B_real
            | "string" ->         B_string
            | "nat" ->            B_int
            | "register" ->       B_reg
            | "bitvector" ->      B_vec (Ord_def,B_bit)
            | _  ->
               (match TBindings.find_opt id ctx.types with
                | Some  (CtxType (ks, target_t,mods,ceks)) -> b_of target_t
                | None -> raise (Failure ("to_ms_base: Typ_app. Not found " ^ id )))
       )
       | Typ_app (Id_aux (Id "atom",_), [ typ_arg ] ) -> B_int
       | Typ_app (Id_aux (Id "range",loc), typ_args ) -> B_int
       | Typ_app (Id_aux (Id "vector_sugar_r",_), [_; len; odr ; A_aux (A_typ typ,_) ]) ->
          B_vec ( convert_order odr , to_ms_base ctx typ)
       | Typ_app (Id_aux (Id "vector",_), [ len; odr ; A_aux (A_typ typ,_) ]) ->
          B_vec ( convert_order odr , to_ms_base ctx typ)
       | Typ_app (Id_aux (Id "int",_), [typ_arg]) ->  B_int
       | Typ_app (Id_aux (Id "atom_bool",_), [typ_arg]) ->   B_bool
       | Typ_app (Id_aux (Id "list",_), [ A_aux (A_typ typ,_)] ) -> B_list (to_ms_base ctx typ)
       | Typ_app (Id_aux (Id "implicit", _), _) -> B_int (* FIXPE *)
       | Typ_app (Id_aux (Id "register",_), [typ_arg]) ->   B_int
       | Typ_app (Id_aux (Id "bitvector",_), [len ; odr]) ->   B_vec ( convert_order odr, B_bit)
       | Typ_app (Id_aux (Id s,_), _ ) -> 
          (match TBindings.find_opt s ctx.types with
           | Some (CtxType (ks,t,_,_)) -> b_of t
           | None -> raise (Failure ("Lookup tid " ^ s)))
       | Typ_tup ts ->
          let bs = List.map (fun t -> to_ms_base ctx t) ts in
          B_tuple bs
       | Typ_exist (kids, cons, typ ) -> to_ms_base ctx typ
       | Typ_var (Kid_aux (Var x,_)) -> B_var x
       | _ -> raise (Failure ( "Unhandled typ " ^ (pp_location loc)))

let lookup_kind_id ctx id = match KABindings.find_opt id ctx.kind_abbrev with
                                    Some (CtxKind (_,ce,_,_)) -> Some ce
                                | None -> None

let to_ms_uop = function
  | "len" -> Len
  | "abs" -> Abs

let to_ms_bop = function
  | "div" -> Div
  | "mod" -> Mod
                                            
let rec to_ms_ce ctx ((A.Nexp_aux (typ,loc)) : A.nexp ) : cep = match typ with
  | Nexp_id (Id_aux (Id id,_)) -> (match (lookup_kind_id ctx id) with
                                          Some ce -> ce
                                      | None -> raise (Failure ("to_ms_ce Nexp_id id=" ^ id)))
  | Nexp_var kid -> CE_val (V_var (VNamed (convert_kid kid)))
  | Nexp_constant num ->  (CE_val (V_lit (L_num ( num ))))
  | Nexp_app (Id_aux (Id id,_) ,[arg1] ) ->
     let ce = to_ms_ce ctx arg1 in
     CE_uop (to_ms_uop id, ce)
  | Nexp_app (Id_aux (Id id,_) ,[arg1;arg2] ) ->
     let ce1 = to_ms_ce ctx arg1 in
     let ce2 = to_ms_ce ctx arg2 in
     CE_bop (to_ms_bop id, ce1, ce2)
  | Nexp_app (Id_aux (Id id,_), _) -> raise (Failure ("to_ms_ce Nexp_app id=" ^ id) )
  | Nexp_times (a1,a2) -> let e1 = to_ms_ce ctx a1 in
                          let e2 = to_ms_ce ctx a2 in CE_bop (Times, e1, e2)
  | Nexp_sum (a1 ,a2) -> let e1 = to_ms_ce ctx a1 in
                         let e2 = to_ms_ce ctx a2 in CE_bop (Plus, e1, e2)
  | Nexp_minus (a1,a2) -> let e1 = to_ms_ce ctx a1 in
                          let e2 = to_ms_ce ctx a2 in CE_bop (Minus, e1, e2)
  | Nexp_exp a1        -> let e1 = to_ms_ce ctx a1 
                          in CE_uop (Exp, e1)
  | Nexp_neg a1        -> let e1 = to_ms_ce ctx a1 
                          in CE_uop (Neg, e1)


                                 
let rec invert_ce (mod0 : (cep*cep) list) ( k : xp) ( ce1 : cep) ( ce2 : cep ) : ( (cep*cep) list * cep ) = match ce2 with
  | CE_bop ( Plus , e1 , e2)  -> (match (contains_var e1 k , contains_var e2 k ) with
                                  | (true,true) -> raise (Failure "Case not handled by inverter")
                                  | (true,_) -> invert_ce mod0 k (CE_bop ( Minus , ce1 , e2)) e1
                                  | (_ , true) -> invert_ce mod0 k (CE_bop (Minus , ce1 , e1)) e2
                                  | (false,false) -> raise (Failure "Existential unconstrained"))

  | CE_bop ( Minus , e1 , e2)  -> (match (contains_var e1 k , contains_var e2 k ) with
                                | (true,_) -> invert_ce mod0 k (CE_bop ( Plus , ce1 , e2)) e1
                                | (_ , true) -> invert_ce mod0 k (CE_uop (Neg, CE_bop (Minus , ce1 , e1))) e2
                                | (false,false) -> raise (Failure "Existential unconstrained") )

  | CE_bop ( Times , e1 , e2)  -> (match (contains_var e1 k , contains_var e2 k ) with
                                   | (true,true) -> raise (Failure "Case not handled by inverter")
                                   | (true,_) -> invert_ce ((ce1,e2)::mod0) k (CE_bop ( Div , ce1 , e2)) e1
                                   | (_ , true) -> invert_ce ((ce1,e1)::mod0) k (CE_bop (Div , ce1 , e1)) e2
                                   | (false,false) -> raise (Failure "Existential unconstrained") )

  | CE_val (V_var _ ) -> (mod0,ce1)
  | CE_val (V_lit _ ) -> raise (Failure "Existential unconstrained") 

                       
               
                                                                 

(*                
let convert_nexp_v n = match n with
  | A.Typ_var (Kid_aux (Var s,l)) -> let _ = if !Tracing.opt_verbosity > 0 then
                                                Printf.eprintf "Loc of var=%s\n" (pp_location l) in
                                      (V_var (convert_loc l, VNamed (convert_to_isa s)))
  | Typ_constant n -> convert_num n 
  | Typ_id _ -> raise (Failure "Atyp_id")
  | _ -> raise (Failure "convert_nexp ")

let convert_nexp_e n = CE_val (convert_nexp_v n)

                                  
let rec convert_nexp ((Typ_aux (n,_)) : A.atyp) : ce = match n with
  | A.Typ_sum (n1,n2) -> CE_bop (Plus, convert_nexp n1, convert_nexp n2)
  | A.Typ_minus (n1,n2) -> CE_bop (Minus, convert_nexp n1, convert_nexp n2)
  | A.Typ_exp (n1) -> CE_uop (Exp, convert_nexp n1)
  | A.Typ_neg (n1) -> CE_uop (Neg, convert_nexp n1)
  | A.Typ_times (n1, n2) -> CE_bop (Times, convert_nexp n1, convert_nexp n2)
  | _ -> CE_val (convert_nexp_v n)
 *)

and  ninc ce = CE_bop (Plus, ce, CE_val (V_lit (L_num (Z.one))))   

(*
let rec to_ms_constraint (A.Typ_aux (aux,l) as atyp) = match aux with
  | A.Typ_app (Id_aux (DeIid op, _), [t1; t2]) ->
       begin match op with
       | "==" -> c_eq (to_ms_ce t1) (to_ms_ce t2)
       | "!=" -> C_not (c_eq (to_ms_ce t1) (to_ms_ce t2))
       | ">=" -> c_ge (to_ms_ce t1) (to_ms_ce t2)
       | "<=" -> c_le  (to_ms_ce t1) (to_ms_ce t2)
       | ">" -> c_ge  (to_ms_ce t1) (ninc (to_ms_ce t2))
       | "<" -> c_le  (to_ms_ce t1) (ninc (to_ms_ce t2))
       | "&" -> C_conj (to_ms_constraint t1,to_ms_constraint t2)
       | "|" -> C_disj (to_ms_constraint t1,to_ms_constraint t2)
       | _ -> raise (Reporting.err_typ l ("Invalid operator in constraint"))
       end
(*    | A.Typ_lit (A.L_aux (A.L_true, _)) -> C_true
    | A.Typ_lit (A.L_aux (A.L_false, _)) -> C_false*)
    | A.Typ_nset (kid, bounds) ->
       let rec convert_eet ns = match ns with
           [] -> C_false
         | n::ns -> C_disj ( c_eq (CE_val (V_var (Loc_unknown,VNamed (convert_kid kid)))) (CE_val (convert_num n)), convert_eet ns)
     in convert_eet bounds
    | _ -> raise (Failure ("Invalid constraint" ^ (pp_location l)))
                      *)


                      
and  to_ms_constraint ctx ( A.NC_aux(nc,_)  : A.n_constraint) : cp = match nc with
  | A.NC_equal (n1,n2) -> c_eq  (to_ms_ce ctx n2) (to_ms_ce ctx n1)
  | A.NC_bounded_ge (n1,n2) -> c_ge  (to_ms_ce ctx n2) (to_ms_ce ctx n1)
  | A.NC_bounded_le (n1,n2) -> c_le  (to_ms_ce ctx n1) (to_ms_ce ctx n2)
  | A.NC_bounded_gt (n1,n2) -> c_gt  (to_ms_ce ctx n2) (to_ms_ce ctx n1)
  | A.NC_bounded_lt (n1,n2) -> c_lt  (to_ms_ce ctx n1) (to_ms_ce ctx n2)
  | A.NC_not_equal (n1,n2) -> C_not (c_eq (to_ms_ce ctx n2) (to_ms_ce ctx n1))
  | A.NC_set (kid, numlist ) ->
     let rec convert_eet ns = match ns with
         [] -> C_false
       | n::ns -> C_disj ( c_eq (CE_val (V_var (VNamed (convert_kid kid)))) (CE_val (convert_num n)), convert_eet ns)
     in convert_eet numlist
  | A.NC_or (nc1,nc2) -> C_disj (to_ms_constraint ctx nc1, to_ms_constraint ctx nc2)
  | A.NC_and (nc1,nc2 ) -> C_conj (to_ms_constraint ctx nc1, to_ms_constraint ctx nc2)
  | NC_app _ -> raise (Failure "to_ms_constraint ctx NC_app")
  | NC_var _ -> raise (Failure "to_ms_constraint ctx NC_var")
  | NC_true -> C_true
  | NC_false -> C_false 


let normalise_record_type fd_type =
  let (f_b,cs) = unzip (List.map (fun (f, T_refined_type(_,b,c)) -> ((f,b),
                     subst_c_v0 c (V_proj (f, V_var (zvar))))) fd_type) in
  let c = Minisailplus_ast.Contexts.conj cs in
  T_refined_type (zvar , B_record f_b , c)

                                                                                                              
let targ_to_nexp (A.A_aux (A_nexp ne,_)) = ne

type ('a, 'b) either  = Left of 'a | Right of 'b

(* Do the substition for the type application. Restrictions on what can be subst for Int type variables *)
let tsubst_t_list typ args = List.fold_left (
        fun typ (actual_arg,formal_arg) ->
        let (x2,(b2,c2)) = formal_arg in
        match actual_arg with
          Left (T_refined_type (_,b1,c1)) ->
          (match b2 with
            B_var bv -> tsubst_tp b1 bv typ
          | _ -> let (T_refined_type (z,b3,c3)) = typ in
                 T_refined_type( z,b3,C_conj (c3,subst_cp (V_var (x2)) zvar c1)))
        | Right (CE_val v) ->
           Printf.eprintf "tsbust_t_list Left\n";
           let T_refined_type (z,b3,c3) = typ in
           T_refined_type (z,b3, subst_cp v x2 c3 )
 ) typ args

(* FIXPE - Need to handle ks *)
let normalise_tlist ts = let (bs,cs) =  unzip  (List.mapi (fun i (T_refined_type (ks , b, c)) ->
                                                    (b, subst_c_v0 c
                                                          (V_proj (convert_to_isa ((string_of_int (List.length ts)) ^ "X" ^ (string_of_int (i+1))),
                                                                   (V_var (zvar) ))))) ts)
                         in (bs,Minisailplus_ast.Contexts.conj cs)


       

let rec convert_to_c_exp ctx (A.A_aux (ae,_)) = match ae with
  | A_nexp ne -> let e = to_ms_ce ctx ne in C_eq (CE_val (V_var (VIndex)), e)
  | A_bool nc -> let e = to_ms_ce_bool ctx nc in C_eq (CE_val (V_var (VIndex)), e)

and to_ms_ce_bool ctx ( A.NC_aux(nc,loc)  : A.n_constraint)  = match nc with
  | A.NC_equal (n1,n2) -> CE_bop (Eq,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_bounded_ge (n1,n2) -> CE_bop (GEq,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_bounded_gt (n1,n2) -> CE_bop (GT,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_bounded_le (n1,n2) -> CE_bop (LEq,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_bounded_lt (n1,n2) -> CE_bop (LT,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_not_equal (n1,n2) -> CE_bop (NEq,  (to_ms_ce ctx n1), (to_ms_ce ctx n2))
  | A.NC_or (nc1,nc2) -> CE_bop (Or, to_ms_ce_bool ctx nc1, to_ms_ce_bool ctx nc2)
  | A.NC_and (nc1,nc2) -> CE_bop (And, to_ms_ce_bool ctx nc1, to_ms_ce_bool ctx nc2)
  | A.NC_true -> CE_val (V_lit L_true)
  | A.NC_false -> CE_val (V_lit L_false)
  | A.NC_app (Id_aux (Id "not", loc), [ A.A_aux (A_bool nc, _ ) ]) -> CE_uop (Not , to_ms_ce_bool ctx nc)
  | A.NC_var kid -> CE_val (V_var (VNamed (convert_kid kid)))
  | A.NC_set _  -> raise (Failure ("to_ms_ce_bool ctx unknown case NC_set " ^ (pp_location loc) ))
                        
and  convert_to_len_exp ctx (A.A_aux (A_nexp ne,_)) = let e = to_ms_ce ctx ne in C_eq (CE_uop (Len, CE_val (V_var (VIndex ))), e)

let rec to_ms_kind (A.KOpt_aux (kid,loc) : A.kinded_id ) : string * bp = match kid with
  (*                                   | KOpt_none (Kid_aux (Var kid,_)) -> (kid,B_int)*)
                                   | KOpt_kind (K_aux (K_int,_), (Kid_aux (Var kid,_))) -> (kid,B_int)
                                   | KOpt_kind (K_aux (K_bool,_), (Kid_aux (Var kid,_))) -> (kid,B_bool)
                                   | KOpt_kind (K_aux (K_type,_), (Kid_aux (Var kid,_))) -> (kid,B_var (convert_to_isa kid))
                                   | KOpt_kind (K_aux (K_order,_), (Kid_aux (Var kid,_))) -> (kid,B_bool) (* FIXPE *)
                                   | _ -> raise (Failure ("Unknown kopt " ^ (pp_location loc)))



and replace_k_in_c k e c = ce_subst_cp e k c

and replace_ks_in_c ( kcs : (xp*cep) list) ( c  : cp ) : cp = List.fold_left (fun c (k,e) -> match k with
                                                           (*                                                           | None -> c*)
                                                           | VNamed  k -> ce_subst_cp e (VNamed k) c) c kcs

and replace_ks_in_funcl ( kcs : (xp*cep) list ) funcl = List.fold_left (fun funcl (k,e) -> ce_subst_funclp e (k) funcl) funcl kcs

                                                                              
(* Extract equations from Sail type *)
let rec extract_equations_typ ctx   (zvr : cep ) ((A.Typ_aux (typ,_)) as typ' : A.typ) =
  Printf.eprintf "extract_eq: %s\n" ( Ast.show_typ typ');
  match typ with
  | A.Typ_id (Id_aux (Id id,_)) when List.mem id ["unit"; "bit"; "string"; "real"; "bool"; "int";"nat"] -> []
  | A.Typ_app (Id_aux (Id id,_), [ typ_arg ] ) when List.mem id ["bool"; "int";"atom";"atom_bool";"implicit"] ->
     extract_equations_typ_arg ctx zvr typ_arg
  | A.Typ_app (Id_aux (Id id,_), [ typ_arg ] ) when List.mem id ["register"] -> []
  | A.Typ_app (Id_aux (Id "vector",_), ( [ len_arg ; ord_arg ; base_arg ] ) ) ->
     extract_equations_typ_arg ctx (CE_uop (Len, zvr)) len_arg
  | A.Typ_app (Id_aux (Id "bitvector",_), ( [ len_arg ; ord_arg  ] ) ) ->
     extract_equations_typ_arg ctx (CE_uop (Len, zvr)) len_arg
  | A.Typ_app (Id_aux (Id "range",_) , _) -> []
  | A.Typ_tup ts ->
     List.concat (List.mapi (fun i t -> extract_equations_typ ctx (CE_proj (mk_proj_op (List.length ts) (i+1), zvr)) t ) ts)
  | A.Typ_app (Id_aux (Id id,_), typ_args ) ->
     (match TBindings.find_opt id ctx.types with
      | Some  (CtxType (ks, target_t,mods,ceks)) -> (* FIXPE FIXPE. Making assumption about ordering and length of ceks/ks/typargs *)
         let ces = List.concat (List.map (fun ((k,(b,c)),ta) -> match b with
                                                                B_int -> [to_ms_ce ctx (targ_to_nexp ta)]
                                                               | _ -> []) (zip ks typ_args)) in
         let ces = List.map (fun (ce1,(Some k,ce2)) -> (ce1,ce_subst_cep zvr xvar ce2 )) (zip ces ceks) in
         List.iter (fun (ce1,ce2) -> pp_line (pp_cep ce1 ^^ (string "==>") ^^ pp_cep ce2)) ces;
         ces
      | None -> raise (Failure ("extract_equations_typ: Typ_app. Not found " ^ id )))
  | A.Typ_id (Id_aux (Id id,_)) ->
     (match TBindings.find_opt id ctx.types with
      | Some  (CtxType (ks, target_t,mods,ceks)) -> []
      | None -> raise (Failure ("extract_equations_typ: Typ_id. Not found " ^ id )))

  | A.Typ_var _ -> []


                 
and extract_equations_typ_arg ctx (zvr : cep ) ( typ_arg : A.typ_arg ) = 
  let (C_eq (_ , ce)) = convert_to_c_exp ctx typ_arg in [(ce,zvr)]
(*
let rec zip_option (xs : 'a list) (ys : 'b) : ('a option * 'b) list = match (xs,ys) with
    ([],[]) -> []
  | (x::xs,y::ys) -> (Some x, y) :: (zip_option xs ys)
  | ([],y::ys) -> (None, y) :: (zip_option [] ys)
 *)

let rec extract_constraints_typ ctx   (zvr : cep ) ((A.Typ_aux (typ,_)) as typ' : A.typ) : cp list =
  match typ with
  | A.Typ_id (Id_aux (Id id,_)) when List.mem id ["nat"] -> [ c_le (CE_val (V_lit (L_num (Z.zero)))) zvr ]
  | A.Typ_app (Id_aux (Id "range",_) , [ nexp1 ; nexp2] ) ->
     let (e1,e2) = (to_ms_ce ctx (targ_to_nexp nexp1) ,to_ms_ce ctx (targ_to_nexp nexp2)) in
     [ mk_range_c_ce zvr e1 e2 ]
  | A.Typ_tup ts ->
     List.concat (List.mapi (fun i t -> extract_constraints_typ ctx (CE_proj (mk_proj_op (List.length ts) (i+1), zvr)) t ) ts)
  | _ -> []
                                                      
let rec zip_partial (xs : 'a list) (ys : 'blist) : ('a * 'b) list * ('b list) = match (xs,ys) with
  | ([],[]) -> ([],[])
  | (x::xs,y::ys) -> let (ws,vs) = zip_partial xs ys in ( (x,y)::ws, vs)
  | ([],ys) -> ([],ys)

(* Pull out the cep pairs that are basic equalities - no need to run these through the solver *)
let filter_bool_ces ( ces : (cep * cep ) list ) (kids : (xp*bp) list) =
  let kids = List.fold_left (fun ks (k,b) -> match b with B_int -> k::ks | _ -> ks ) [] kids in
  let (ces1,ces2,kids) = List.fold_left (fun (ces1,ces2,kids) (ce1,ce2) -> match ce1 with
                                                                             (CE_val (V_var k)) -> ((k,ce2)::ces1,ces2,kids)
                                                                           | _ -> (ces1,(ce1,ce2)::ces2,kids)) ([],[],[]) ces in
 (ces1,ces2, kids)
                                 
let rec extract_pp ctx ( kids : (xp*bp) list ) ( typ : A.typ) : ( xp * cep ) list * cp list =
  (*  let kids =   List.map (fun k -> let (k,b) = to_ms_kind k in (VNamed k)) kids' in*)
  let ces = extract_equations_typ ctx (CE_val (V_var zvar)) typ in
  let (ceks', ces, kids) = filter_bool_ces ces kids in
  let cs = extract_constraints_typ ctx (CE_val (V_var zvar)) typ in
  Printf.eprintf "** extract_pp ** \n";
  List.iter ( fun (ce1,ce2) -> pp_line (pp_cep ce1 ^^ (string " = ") ^^ (pp_cep ce2))) ces;
  List.iter ( fun (ce1,ce2) -> pp_line (pp_raw_cep ce1 ^^ (string " = ") ^^ (pp_raw_cep ce2))) ces;  
  List.iter ( fun (c) -> pp_line (pp_raw_cp c)) cs;
  Printf.eprintf "#kids=%d\n" (List.length kids);
  if kids = [] & ces = [] then (ceks', cs) else
  match solve_ce_ce kids ces with
  | Some (ces,mods) -> List.iter ( fun ce1 -> pp_line (pp_cep ce1 )) ces;
                if List.length kids > List.length ces then raise (Failure "Mising equalities")
                else let (ceks,ce) = zip_partial kids ces in
                     let cs = replace_ks_in_c ceks (C_conj_many cs) in
                     (ceks@ceks', cs :: mods @ List.map (fun ce -> C_eq ((CE_val (V_lit (L_num (Z.zero)))),ce)) ce)
  | None -> raise (Failure "Linear Solver Failed")
                           
                                           
(*
and convert_invert kid e1 typ_arg c =
  let (C_eq (_ , c_exp)) = convert_to_c_exp typ_arg in
  let (mods,e1) = invert_ce [] (VNamed kid) e1 c_exp in
  PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_c c);
  PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_cep e1);
  let mods = C_conj_many (List.map (fun (x,y) -> C_eq ( CE_bop (Mod , x,y), CE_val (V_lit (L_num (int_of_int 0))))) mods) in
  Printf.eprintf "k=%s\n" kid;
  let c = replace_k_in_c (VNamed kid) e1 c in
  let c =C_conj (mods, c) in 
  PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_c c);
  c
 *)
                                      
and convert_invert_typ_arg ctx (kids : string list)  (e1 : cep ) ( typ_arg : A.typ_arg ) 
    :  (cep * cep ) list * ((string option) * cep)
  =
  let (C_eq (_ , ce)) = convert_to_c_exp ctx typ_arg in
  let fs = List.filter (fun k -> contains_var ce (VNamed k)) kids in
  let (mods,kid,e1) = match fs with
    | [] -> ([],None,ce)
    | [kid] -> let (mods,e1) = invert_ce [] (VNamed kid) e1 ce in
               (mods ,Some kid,e1)
    | (_::_) -> raise (InvertFail) (*Failure "Expression contains more than one type level variable")*)
  in
  Printf.eprintf "convert_invert_typ_arg ce= e1=\n";
  PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_cep ce); Printf.eprintf "\n";
  PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_cep e1); Printf.eprintf "\n";
  (mods,(kid,e1))

    
and convert_invert_typ ctx ( kids : string list)  (zvar : cep ) ((A.Typ_aux (typ,loc)) as typ' : A.typ)
    : mods * ceks *  (cp list) =
  Printf.eprintf "convert_invert_typ: %s"; (Ast.show_typ typ');
  match typ with
  | A.Typ_var _ -> ([],[],[])
                     
  | A.Typ_id (Id_aux (Id id,_)) when List.mem id ["unit";"bit";"bool";"int";"nat";"string";"real"] -> ([],[],[]) (* FIXPE nat needs a constraint *)
  | A.Typ_id (Id_aux (Id id,_)) ->
     (match TBindings.find_opt id ctx.types with
      | Some  (CtxType (ks, target_t,mods,ceks)) ->
         Printf.eprintf "typ_app |ceks|=%d\n" (List.length ceks);
         let (mods,ceks) =
           if List.length ceks = 0 then
             ([],[])
           else unzip (List.map (fun ((Some _,ce),ta) -> convert_invert_typ_arg ctx kids ce ta) ([])) in
         (List.concat mods, ceks,[]))
           
  | A.Typ_app (Id_aux (Id id,_), [ typ_arg ] ) when List.mem id ["bool"; "int";"atom";"atom_bool"] ->
     let (mods,ce) = convert_invert_typ_arg ctx kids zvar typ_arg in
     (mods,[ce],[])
  | A.Typ_app (Id_aux (Id "vector",_), ( [ len_arg ; ord_arg ; base_arg ] ) ) ->
     let (mods,ce) = convert_invert_typ_arg ctx kids (CE_uop (Len, zvar)) len_arg in
     (mods,[ce],[])
  | Typ_app (Id_aux (Id "range",loc), [ lhs_arg; rhs_arg] ) ->
     let (_, (_,ce_left)) = convert_invert_typ_arg ctx kids zvar lhs_arg in
     let (_, (_,ce_right)) = convert_invert_typ_arg ctx kids zvar rhs_arg in
     (match (fvs_cep ce_left, fvs_cep ce_right) with
     | ([],[]) -> ([],[], [mk_range_c_ce zvar ce_left ce_right] )
     | _ -> raise (Failure "Arguments to 'range' need to be constants"))
  | Typ_app (Id_aux (Id "bitvector",_) , [ len_arg; ord_arg ] ) ->
     let (mods,ce) = convert_invert_typ_arg ctx kids (CE_uop (Len, zvar)) len_arg in
     (mods,[ce],[])       
  | A.Typ_app (Id_aux (Id "list",_), ( [base_arg ] )) ->  ([],[],[])
  | A.Typ_app (Id_aux (Id id,_), typ_args ) ->
     (match TBindings.find_opt id ctx.types with
      | Some  (CtxType (ks, target_t,mods,ceks)) ->
         Printf.eprintf "typ_app |ceks|=%d\n" (List.length ceks);
         let (mods,ceks) =
           if List.length ceks = 0 then
             ([],[])
           else unzip (List.map (fun ((Some _,ce),ta) -> convert_invert_typ_arg ctx kids ce ta) (zip ceks typ_args)) in
         (List.concat mods, ceks,[])
      | None -> raise (Failure ("convert_invert_typ: Typ_app. Not found " ^ id )))
        
     
  | A.Typ_tup ts ->
     let (mods,ces,cs) = unzip3 (List.mapi (fun i t -> convert_invert_typ ctx kids (CE_proj (mk_proj_op (List.length ts) (i+1), zvar)) t ) ts) in
     (List.concat mods, List.concat ces, List.concat cs)
  | _ -> raise (Failure ("convert_invert_typ: Unknown typ " ^ pp_location loc))

(*       
and to_ms_exist_one_rec loc ctx kid b c typ = 
  let (A.Typ_aux (typ,_)) = typ in
  match typ with
  | A.Typ_app (Id_aux (Id "atom",_), [ typ_arg ] ) ->
     let c = convert_invert kid (CE_val (V_var zvar)) typ_arg c in
     T_refined_type ([],zvar,B_int, c )
  | A.Typ_app (Id_aux (Id "vector",_), ( [ len_arg ; ord_arg ; base_arg ] ) ) ->
     let c = convert_invert kid (CE_uop (Len, CE_val (V_var zvar))) len_arg c in
     let ord = convert_order ord_arg in
     T_refined_type( [], zvar, B_vec (ord,B_bit), c )
  | A.Typ_tup ts ->
     let ts = List.map (to_ms_exist_one_rec loc ctx kid b C_true) ts in
     let (bs,c) = normalise_tlist ts in
     Printf.eprintf "After normalise\n";
     PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_c c);
     T_refined_type ([],zvar,B_tuple bs, c)
 *)

and to_ms_exist_many loc ctx (kids : A.kinded_id list) (cons : A.n_constraint) (typ : A.typ) : tau =
  Printf.eprintf "to_ms_exist_many %s\n" (pp_location loc);
  let c = to_ms_constraint ctx cons in
  let kids = List.map to_ms_kind kids in
  let kids = List.filter (fun (x,b) -> match b with
                                           | B_int -> true
                                           | B_bool -> true
                                           | _ -> false) kids in
  let kids = List.map (fun (x,b) -> (VNamed x,b)) kids in
  let (t,_) = to_ms_exist_many_aux ctx loc kids c typ in
  t

(* 
   ceks is a list of (kid,ce) such that kid = ce,
   kid is either bool or int Sail type variable
   cs1 is a list of additional constraints arising from linear solving
   mods is a list of mod constraints arising from use of div 
*)    
and to_ms_exist_many_aux ctx loc (kids : (xp*bp) list) (c : cp) (typ : A.typ)  =
  Printf.eprintf "to_ms_exist_many_aux %s\n" (pp_location loc);
  let int_kids = List.fold_left (fun ks (x,b) -> match b with
                                                 | B_int -> (x,b)::ks
                                                 | B_bool -> (x,b)::ks
                                           | _ -> ks) [] kids in
  let (ceks,cs1) = extract_pp ctx int_kids typ in (*convert_invert_typ ctx kids (CE_val (V_var xvar)) typ in*)
  let mods = [] in
  List.iter (fun (k,e1) -> match k with
                           | VNamed k -> Printf.eprintf "k=%s\n" k; pp_line (pp_cep e1)
    ) ceks;
  let cs = replace_ks_in_c ceks c in
 (* 
  let mods = List.map (fun (x,y) -> C_eq ( CE_bop (Mod , x,y), CE_val (V_lit (L_num (int_of_int 0))))) mods in
  let c_z_eq = [] (*map_concat (fun (k,e) -> match k with
                                    | None -> [C_eq (CE_val (V_var zvar),e)]
                                    | Some _ -> []) ceks in*)
  let ceks = map_concat (fun (k,e) -> match k with
                                    | None -> []
                                    | Some k -> [(k,e)]) ceks in
  let ceks' = merge_assoc ceks in
  let c_eq = List.concat (List.map (fun k -> match List.assoc_opt k ceks' with
                                | Some (ce::ces)  -> List.map (fun ce' -> C_eq (ce,ce')) ces
                                | Some _ -> []
                                | None -> raise (Failure ("No equation for type variable " ^ k ))
                            ) kids) in 
  let t =   T_refined_type( zvar, to_ms_base ctx typ, C_conj_many (cs :: mods @ c_eq @ c_z_eq @ cs2)) in *)
  let t =   T_refined_type( zvar, to_ms_base ctx typ, C_conj_many (cs::cs1) ) in 
  PPrintEngine.ToChannel.compact stderr ((string "to_ms_exist_many result=\n") ^^ Minisailplus_pp.pp_tp t ^^ (string "\n"));
  (t,ceks)
                                 
                          
(*
  let c_eq = match ces with
    | ce::ces -> List.map (fun ce' -> C_eq (ce,ce')) ces
    | _ -> [] in

  T_refined_type( [], zvar, to_ms_base typ, C_conj_many (mods @ cs @ c_eq))*)

                
and to_ms_exist loc ctx kids cons typ : tau = match kids with
  | [] -> to_ms_typ ctx typ
  | kids -> to_ms_exist_many loc ctx kids cons typ
  | _ -> raise (Failure "More than one existential variable")


       
(* Allow many existentials *)                              
and to_ms_exist_allow_many loc ctx kids cons typ = 
  (* The FIXPE kids are all ints ? *)
  let c = to_ms_constraint ctx cons in 
  
  let rec convert_kid kids  = List.map (fun k -> let (k,b) = to_ms_kind k in (VNamed k, (b,C_true))) kids in
  let local_ctx = List.fold_left (fun ctx (A.KOpt_aux (kinded_id,_))  ->
                      let (kid,kind) = (match kinded_id with
                                        (*                                | KOpt_none (Kid_aux (Var kid,_)) -> (kid,A.K_int)*)
                                        | KOpt_kind (K_aux(kind,_), (Kid_aux (Var kid,_))) -> (kid,kind))
                      in  { ctx with kinds = KBindings.add kid (A.K_aux (kind,loc)) ctx.kinds }) ctx kids in
  
  let T_refined_type (_,b,c2) = to_ms_typ local_ctx typ
  in T_refined_type (zvar,b,C_conj (c,c2))

(* Do type constructor application. Curently only support Type and Int type level arguments *)                    
and to_ms_typ_app ctx loc id typ_args =
  Printf.eprintf "Typ_app %s (%s)\n" id (pp_location loc);
  
  (match TBindings.find_opt id ctx.types with
           | Some  (CtxType (ks, target_t,_,_)) -> 
              Printf.eprintf "  |typ_args|=%d |ks|=%d\n" (List.length typ_args) (List.length ks);
              let typ_args = List.map (fun ta ->
                                 match ta with
                                 | A.A_aux (A_typ t,_) -> Left (to_ms_typ ctx t)
                                 | A.A_aux (A_nexp n,_) -> Right (to_ms_ce ctx n)
                               ) typ_args in
              let ksb = zip typ_args ks in 
              tsubst_t_list target_t ksb
           | None -> raise (Failure "to_ms_typ"))

                                            
and  to_ms_typ ctx (A.Typ_aux (typ,loc)) : tau =
  Printf.eprintf "to_ms_typ %s\n" (pp_location loc);
  match typ with
       | A.Typ_id (Id_aux (Id s,loc2)) -> (match s with
              "int" -> T_refined_type ( zvar , B_int, C_true)
            | "bool"|"boolean" -> T_refined_type (zvar,B_bool, C_true)
            | "reg_size" ->       T_refined_type (zvar,B_int, C_true) (* FIXPE *)                             
            | "unit" ->           T_refined_type (zvar,B_unit, C_true)
            | "bit" ->            T_refined_type (zvar,B_bit, C_true)
            | "real" ->           T_refined_type (zvar,B_real, C_true)
            | "string" ->         T_refined_type (zvar,B_string, C_true)
            | "nat" ->            T_refined_type (zvar,B_int, c_le (CE_val (V_lit (L_num (Z.zero))))
                                                           (CE_val (V_var zvar)))
            | _ -> 
               Printf.eprintf "Lookup tid loc = %s %s\n" (pp_location loc2) s;
               (match TBindings.find_opt s ctx.types with
                | Some (CtxType (ks,t,_,_)) -> t
                | None -> raise (Failure "Lookup tid"))
                                           )
       | Typ_var (Kid_aux (Var kid,_)) ->
          (match (KBindings.find_opt kid ctx.kinds) with
           | Some (K_aux(kd,_)) -> 
              (match kd with 
               | A.K_int -> T_refined_type(zvar,B_int , c_eq (CE_val (V_var (zvar))) (CE_val (V_var (VNamed kid))))
               | A.K_type -> T_refined_type(zvar,B_var kid , C_true)
               | _ -> raise (Failure "to_ms_typ Unexpected use of order kind"))
           | None -> raise (Failure (Printf.sprintf "Kind lookup %s failed at %s\n" kid (pp_location loc))))

(*       | Typ_lit lit -> T_refined_type(zvar, B_int, convert_to_c_exp  (A.Typ_aux (typ,loc)))
       | Typ_times _ -> raise (Failure ("to_ms_typ Typ_times"))
       | Typ_sum _ -> raise (Failure ("to_ms_typ Typ_sum"))
       | Typ_minus _ -> raise (Failure ("to_ms_typ Typ_minus"))*)
       | Typ_app (Id_aux (Id "atom",_), [ typ_arg ] ) ->
          let c_exp = convert_to_c_exp ctx typ_arg in  T_refined_type (zvar,B_int, c_exp )
       | Typ_app (Id_aux (Id "range",loc), typ_args ) ->
          (*          let loc = convert_loc loc in *)
          (match typ_args with
             [ ne1; ne2 ] -> 
               let (e1,e2) = (to_ms_ce ctx (targ_to_nexp ne1) , to_ms_ce ctx (targ_to_nexp ne2)) in
               T_refined_type (zvar,B_int, mk_range_c zvar e1 e2)
             |  _ -> raise (Failure ("to_ms_type match typ_args failed " ^ (pp_location loc))))
       | Typ_app (Id_aux (Id "vector_sugar_r",_), [_; len; odr ; A_aux (A_typ typ,_) ]) ->
          let odr = convert_order odr in
          let b = b_of (to_ms_typ ctx typ) in
          T_refined_type ( zvar,B_vec (odr,b), convert_to_len_exp ctx len )
       | Typ_app (Id_aux (Id "vector",_), [ len; odr ; A_aux (A_typ typ,_) ]) ->
          let odr = convert_order odr in
          let b = b_of (to_ms_typ ctx typ) in
          T_refined_type ( zvar,B_vec (odr,b), convert_to_len_exp ctx len )
       | Typ_app (Id_aux (Id "bits",_), [ len]) ->                         (* FIXME? - Don't do this. Let prelude define it and use general lookup. need to handle nexp as typ_arg *)
          (match TBindings.find_opt "bits" ctx.types with
           | Some  (CtxType (ks, target_t,_,_)) ->  T_refined_type ( zvar, b_of target_t, convert_to_len_exp ctx len )
          )
       | Typ_app (Id_aux (Id "int",_), [typ_arg]) ->
          let c_exp = convert_to_c_exp ctx typ_arg in  T_refined_type (zvar,B_int, c_exp )
       | Typ_app (Id_aux (Id "atom_bool",_), [typ_arg]) ->
          let c_exp = convert_to_c_exp ctx typ_arg in  T_refined_type (zvar,B_bool, c_exp )
       | Typ_app (Id_aux (Id "implicit",_), [ A_aux (A_typ typ,_)] ) -> to_ms_typ ctx typ (* FIXPE - Is this how we handle implicit ? *)
       | Typ_app (Id_aux (Id "list",_), [ A_aux (A_typ typ,_)] ) ->
                   let (T_refined_type (zvar, b, _)) = to_ms_typ ctx typ in 
                   T_refined_type (zvar,B_list b, C_true)
       | Typ_app (Id_aux (Id "register",_), [typ_arg]) ->   (* FIXPE Should have a base type for registers ? *)
          let c_exp = convert_to_c_exp ctx typ_arg in  T_refined_type (zvar,B_int, c_exp )
       | Typ_app (Id_aux (Id "bitvector",_), [len; ord]) ->
          let odr = convert_order ord in
          T_refined_type(zvar, B_vec(odr, B_bit), convert_to_len_exp ctx len)
       | Typ_app (Id_aux (Id x, loc) as tid , typ_args) ->
          to_ms_typ_app ctx loc x typ_args
       | Typ_tup ts ->
          let ts = List.map (fun t -> to_ms_typ ctx t) ts in
          let (bs,c) = normalise_tlist ts in 
          T_refined_type (zvar,B_tuple bs, c)
       | Typ_exist (kids, cons, typ ) -> to_ms_exist loc ctx kids cons typ
                            
(*       | Typ_with ( atyp, cons ) ->
          let c =to_ms_constraint ctx cons in
          let T_refined_type (_,_,b,c_typ) = to_ms_typ ctx atyp in
          let kids = Minisailplus_ast.Syntax.fvs_c(c) in (* FIXPE Need to take away forall quantified ? *)
          let kids = List.map (fun x -> (x,(B_int,C_true))) kids in
          let kids = match kids with
              [] -> []
            | (k,(b,_))::xs -> (k,(b,c))::xs in
          T_refined_type ( kids ,zvar,b,c_typ)*)
       (*       | Typ_wild -> T_refined_type ([], zvar,B_int, C_true)*)
       | Typ_fn _ -> raise (Failure ( "Unhandled typ Typ_fn" ^ (pp_location loc)))
       | Typ_bidir _ -> raise (Failure ( "Unhandled typ Typ_bidir" ^ (pp_location loc)))

(* Permit 0 or 1 existential *)
(* FIXPE - We can allow more than one if they are 'separable' ie
   { 'q, 'p , p = q + 1 . ( int('q+1), int('p+2) ) }
leads to
   'q = proj 1 z - 1 
   'p = proj 2 z - 2 
and
   { z : (int,int) | (proj 2 z) = (proj 1 z - 1) + 1 }
 *)

