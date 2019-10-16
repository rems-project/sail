(* 
    Convert from Sail AST to MiniSail AST (the AST as generated from Ott via Isabelle).

    See sail_to_ms.txt for notes on what this does

    Follows outline of sail/initial_check.ml 

    Possibly making more work for myself here than necessary.

    Attempt to get the balance on the path from AST to type checking, where the work is done.
    Convert_ast is doing more work than normal; but this enables a more cleaner
    type checker and since as the tc is generated from inductive rules, cleaner, more mathematical rules. 

    Differences between Sail and MiniSail AST
      In Sail, expressions in constraints use different datatypes than expressions in statements. In
      MiniSail they are the same.

      Sail uses type ids for 'int', 'bool' etc, MiniSail uses constructors B_int, B_bool etc.
      And Sail uses application of type constructors, vec, bits, tuple etc, whilst minisail has base types B_vec, B_tuple

      Sail type schemes vs MiniSail type schemes

    TODO - Make sure all matches are complete and match order of constructors in datatype AST

   Fiddly bits with integers and nats.

   A number of well-formedness conditions are checked for / required:
        Conversion to Nexp. Nexp_id and Nexp_app are not handled   
        Conversion from n_constraint. var and app not handled
 *)

open PPrintEngine
open PPrintCombinators

module A = Ast 
module P = Parse_ast
             
open Util
open Util_ms
(*open Util2*)
open Ast_walker
       
open Minisailplus_ast.SyntaxVCT  (* Mini Sail AST as obtain from Isabelle *)
open Minisailplus_ast.SyntaxPED  (* Mini Sail AST as obtain from Isabelle *)
open Minisailplus_ast.Location
open Minisailplus_ast.Contexts
open Minisailplus_pp

open Convert_typ

exception NotSupported of string;;
       
let add_abbrev ctx id tq typ (mods : mods ) (ceks : ceks) = { ctx with types = TBindings.add id (CtxType (tq,typ,mods,ceks)) ctx.types }

let add_kind ctx id tq ce (mods : mods) ( ceks : ceks ) = { ctx with kind_abbrev = KABindings.add id (CtxKind (tq,ce, mods, ceks)) ctx.kind_abbrev }
                                                              
(*val to_ms_e : ctx -> unit A.exp -> e
val to_ms_e_aux : ctx -> unit A.exp -> P.l -> e*)

let fresh_cnt = ref 0

let fresh_var _ = let x = (VNamed ("xxx" ^ (string_of_int !fresh_cnt))) in
                  fresh_cnt :=  !fresh_cnt + 1;
                  x
                            
(*type env_entry = EType of ((x* (b*c)) list) * tau | EFun of ( ((x* (b*c)) list) *  b * c * tau)*)

let print_tenv ctx = Printf.eprintf "print_tenv\n";
                      TBindings.iter (fun k e -> Printf.eprintf "k=<%s>\n" k) ctx.types
                                              
let rec unzip xs = match xs with
    [] -> ([],[])
  | ((x,y)::xys) -> let (xs,ys) = unzip xys in ( x::xs , y::ys )

                                                 
let list_to_map ls = List.fold_left (fun y (k,(ks,t)) -> TBindings.add (implode k)  (ks,t) y ) TBindings.empty ls

                                 
(*let nat_of_sint i = Arith.Nat (Big_int.big_int_of_string (string_of_int i))*)

                              
let convert_pos (p : Lexing.position) = Pos_ext (convert_to_isa  p.pos_fname, Z.of_int p.pos_lnum, Z.of_int  p.pos_bol, Z.of_int p.pos_cnum, ())


                                                         
let convert_loc (l : A.l) = match l with
  | P.Range (p1,p2) -> Loc_range (convert_pos p1, convert_pos p2)
  | _ -> Loc_unknown
                                 
                           
let convert_id id = match id with
    A.Id_aux (Id id , _ ) -> convert_to_isa id
    | Id_aux (Operator id , _ ) -> convert_to_isa id

let mk_id x = A.Id_aux (Id x , Unknown)

let up_id id = match id with
    A.Id_aux (Id id , _ ) -> id
  | Id_aux (Operator id , _ ) -> id
    
                       

let hex_to_bv (s : char list) =
  List.concat
    ( List.map (fun c ->
          let c = Scanf.sscanf (implode [c]) "%x%!" (fun x -> x) in
          [
            if (c / 8) mod 2 = 0 then L_zero else L_one;
            if (c / 4) mod 2 = 0 then L_zero else L_one;
            if (c / 2) mod 2 = 0 then L_zero else L_one;
            if c mod 2 = 0 then L_zero else L_one
          ]) s)
                                 

                        
let to_ms_lit (A.L_aux (l,loc)) = match l with
  | L_unit -> L_unit
  | L_zero -> L_zero
  | L_one -> L_one
  | L_true -> L_true
  | L_false -> L_false
  | L_num n -> L_num ( n ) (*(Nat_big_num.to_int n)))*)
  | L_hex s -> L_bitvec (hex_to_bv (explode s))
  | L_bin bs -> (L_bitvec (List.map (fun b -> if b = '0' then L_zero else L_one) (explode bs)))
  | L_undef -> L_undef
  | L_string s -> L_string (convert_to_isa s)
  | L_real r -> L_real (convert_to_isa r)

let to_ms_lit_v (A.L_aux (l,loc)) = match l with
  | L_hex s -> V_vec (List.map (fun l -> V_lit l) (hex_to_bv (explode s)))
  | L_bin bs -> (V_vec (List.map (fun b -> if b = '0' then (V_lit L_zero) else (V_lit L_one)) (explode bs)))
  | _ -> V_lit (to_ms_lit (A.L_aux (l,loc)))
                        
(* Convert from atyp to constraint expression *)

let invert_bop bop = match bop with
  | Plus -> Minus
  | Minus -> Plus


(* 
  Consider 'ce1 = ce2' , rewrites this to move terms to the left hand side ensuring the the variable k is left on 
  the right hand side. 
  Any use of div as an inversion of times needs to be recorded to that we can generate a mod expression for it.
*)


let base_of (T_refined_type (_,b,c)) = b

                    
                              
let rec to_ms_typ_schm ctx (A.TypSchm_aux (TypSchm_ts (tq, typ),_)) =
  let (ctx,tq) = to_ms_typquant ctx tq
  in (ctx,tq, to_ms_typ ctx typ)
                              
                                                               

(* Return list of variables and associated types corresponding to quantifier.
Work through quant items, if we hit a Q_id, add to var list with top constraint, if a constraint, then make this the
  constraint for the last var *)

                                                
and  to_ms_typquant ctx ( (A.TypQ_aux (tq,loc)) : A.typquant) =
  let rec convert_qis qis kids = match qis with
      [] -> kids
     | (x::xs) -> match x with
                    (A.QI_aux (QI_constraint nc,_)) -> let c = to_ms_constraint ctx nc in
                                                  let fv = fvs_cp c in
                                                  let kd = List.map fst kids in 
                                                  let fv = List.filter (fun v -> not (List.mem v kd)) fv in
                                                  let fv = List.map (fun v -> (v,(B_int, C_true))) fv in
                                                  let kids = fv@kids in 
                                                  (match kids with
                                                  | (x, (b,c' ))::ks -> convert_qis xs ((x,(b,C_conj (c,c')))::ks)
                                                  | [] -> raise (Failure "to_ms_typquant Constraint with no kid"))
                  | (QI_aux (QI_id kid,_)) -> let (k,b) = to_ms_kind kid in
                                              convert_qis xs ((VNamed (convert_to_isa k),
                                                               (b, C_true)) :: kids)
                  | (QI_aux (QI_constant [kid],_)) -> let (k,b) = to_ms_kind kid in
                                              convert_qis xs ((VNamed (convert_to_isa k),
                                                               (b, C_true)) :: kids)
                  | _ -> raise (Failure ("to_ms_typquant. pattern fail loc=" ^ (pp_location loc)))

  in match tq with
       TypQ_no_forall -> (ctx,[])
     | TypQ_tq qis ->
        let ctx = List.fold_left (fun ctx qi -> match qi with
                                                | (A.QI_aux (QI_id (KOpt_aux(kid, loc)),_)) ->
                                                   (match kid with
                                                      KOpt_kind (kind,(Kid_aux (Var kid,_))) ->
                                                      { ctx with kinds = KBindings.add kid kind  ctx.kinds }
                                                   ) 
                                                | _ -> ctx ) ctx qis
        in (ctx,convert_qis qis [])

let to_ms_fun loc ctx (kids : (xp*(bp*cp)) list) (tin : A.typ) (tout : A.typ) =
  List.iter (fun ((VNamed x,(b,c))) -> Printf.eprintf "k=%s\n" x;
                                       pp_line (pp_bp b)) kids;
  let kids = List.filter (fun (x,(b,c)) -> match b with
                                           | B_int -> true
                                           | B_bool -> true
                                           | _ -> false) kids in
  let c = match kids with
    | ((_,(_,c))::_) -> c
    | _ -> C_true in
  let kids = List.map (fun (x,(b,c)) -> (x,b)) kids in
  (*  let kids = List.map (fun (VNamed x,_) -> VNamed x) kids in*)
  let (tin,ceks) = to_ms_exist_many_aux ctx loc kids c tin in
  let T_refined_type (z,bout, cout ) = to_ms_typ ctx tout in
  let ceks = List.map (fun (k,ce) -> (k,subst_cep (V_var xvar) zvar ce)) ceks in
  Printf.eprintf "ceks are:\n";
  List.iter (fun (VNamed k,ce) -> Printf.eprintf "%s\n" k; pp_line (pp_cep ce)) ceks;
  let cout = replace_ks_in_c ceks cout in
  let tout = T_refined_type(z,bout,cout) in
  Printf.eprintf "convert_fn tin= "; pp_line (pp_tp tin);
  Printf.eprintf "convert_fn tout= "; pp_line (pp_tp tout);
  (b_of tin, subst_cp (V_var xvar) zvar (c_of tin), tout,ceks)

(* Merge with to_ms_typ_schem *)


let convert_tq_typ ctx loc tq typ = match typ with
  | A.Typ_aux (Typ_fn (tin,tout,teff),_) ->
     Printf.eprintf "convert fun %s\n (pp_location loc)";
     let (ctx,kids) = to_ms_typquant ctx tq in
     let tin = (match tin with
                | [tin] -> tin
                | _ -> A.Typ_aux (Typ_tup tin,loc)) in
     (*
     let (T_refined_type (in_kids,in_z,b,c)) = to_ms_typ ctx tin in
     PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_cm c);
     let tout = to_ms_typ ctx tout in
     (kids@in_kids, b, c, tout)
     *)
     let (b,c,tout,ceks) = to_ms_fun loc ctx kids tin tout in
     ([],b,c,tout)
  | A.Typ_aux (Typ_bidir _, _) ->
     raise (NotSupported ("Typ_bidir loc=" ^ (pp_location loc)))
  | _ -> Printf.eprintf "Unknown type scheme pattern %s\n" (pp_location loc);
         Printf.eprintf "%s\n"  (Ast.show_typ typ);
         raise (Failure "Unknown type scheme")

let to_ms_typschm ( ctx : 'a ctx ) (A.TypSchm_aux (TypSchm_ts (tq, typ),loc)) = convert_tq_typ ctx loc tq typ
                                  
let convert_tannot ctx typ = match typ with
  | A.Typ_annot_opt_aux (Typ_annot_opt_some (tq,typ), loc ) ->
     let (kids,b,c,tout) = convert_tq_typ ctx loc tq typ in
     (*     let (ctx,c) = to_ms_typquant ctx tq*)
     Some (ctx,C_true, A_function(xvar, b, c , tout ))
  | A.Typ_annot_opt_aux (Typ_annot_opt_none,_)  -> None

let to_ms_op op = match op with
    "+" -> Plus
  | "<=" -> LEq
  | "=" -> Eq
  | "<"  -> LT
  | "*" -> Times
  | "-" -> Minus
            
                    
(*let rec convert_fexp (loc : A.l) (A.E_aux (exp, _)) = match exp with
   A.E_app_infix (E_aux (E_id (Id_aux (Id id, _ )),_), Id_aux (Id "=",_) , E_aux (arg2,_)) -> (convert_to_isa id , to_ms_v arg2 loc )*)

let rec convert_fexp (loc : A.l) (A.FE_aux (FE_Fexp ( Id_aux (Id id,_) , E_aux( exp, _ ) ), _)) =
  Printf.eprintf "convert_fexp loc= %s\n" (pp_location loc);
  (convert_to_isa id , to_ms_v exp loc )

             

(* FIXME - Attempt to convert E to a value *)                                                                          
and  to_ms_v ( exp : Type_check.tannot  A.exp_aux) loc : vp =
  match exp with
  | A.E_lit l -> to_ms_lit_v l
  | E_id (Id_aux(Id x, loc)) -> V_var (VNamed (convert_to_isa x))
  | E_tuple [ E_aux (exp,l) ] -> to_ms_v exp loc
  | E_id _ -> raise (Failure "Other id")
  | E_lit _ -> raise (Failure "Other lit")                                           
  | E_tuple args -> V_tuple (List.map (fun (A.E_aux(e,(l,_))) -> to_ms_v e l ) args)
  | E_record fexps -> V_record (List.map (convert_fexp loc) fexps)

(*  | E_block [E_aux (exp1,_); E_aux (exp2,_) ] -> let v1 = to_ms_v exp1 loc in  (* Terrible hack. Seems like record constructors are not E_record *)
                                                 let v2 = to_ms_v exp2 loc in
                                                    V_pair (v1,v2)*)
  (*  | E_app _ -> raise (Failure ("Trying to process an App  as a value loc=" ^ (pp_location loc)))*)
                                                                       
(*  | E_internal_let  _ -> raise (Failure "Let")*)

  | E_record _ -> raise (Failure "Record ")


  | E_assign _ -> raise (Failure ("Assign " ^ (pp_location loc)))
  | E_field (E_aux (exp,_), Id_aux(fname,_)) -> raise (Failure "E_field")
  | E_var _ -> raise (Failure ("Expression not handled Sail E_var " ^ (pp_location loc))) (* Internal node *)
  | E_ref _ -> raise (NotSupported ("Expression not handled Sail E_ref" ^ (pp_location loc)))
  (*  | E_deref _ -> raise (Failure ("Expression not handled Sail E_deref" ^ (pp_location loc)))*)
  | E_constraint _ -> raise (Failure ("Expression not handled Sail E_constraint" ^ (pp_location loc)))
  | _ -> raise (Failure ("Expression not handled Sail unknown form" ^ (pp_location loc)))

let tick_var ( s : string ): bool = match (explode s) with
    [] -> false
  | x::xs -> (x = (Char.chr(96)))
               
(* Converts the <pat> as <typ> construct *)
let rec to_ms_pat_as_typ ctx pat (A.Typ_aux (typ,loc) as full_typ) = match typ with
  | Typ_id (Id_aux (Id id,_)) -> if (tick_var id) then
                                    Pp_as_typ( convert_loc loc, to_ms_pat ctx pat,
                                                   T_refined_type(zvar, B_int, c_eq_x (VNamed (convert_to_isa id)) zvar))
                                  else
                                    Pp_as_var( convert_loc loc, to_ms_pat ctx pat,
                                      VNamed (convert_to_isa id))
                                                     
  | _ -> Pp_as_typ (convert_loc loc, to_ms_pat ctx pat, to_ms_typ ctx full_typ)

and  to_ms_pat ctx (A.P_aux (pat,(loc,_)) as full_pat) : patp = match pat with
  | P_lit l -> Pp_lit (convert_loc loc, to_ms_lit l)
  | P_wild -> Pp_wild (convert_loc loc)
  | P_or _ -> raise (Failure ("to_ms_pat Or patterns not handled " ^ (pp_location loc)))
  | P_not _ -> raise (Failure ("to_ms_pat Not patterns not handled " ^ (pp_location loc)))
  | P_as _ -> raise (Failure ("to_ms_pat As patterns not handled " ^ (pp_location loc)))
  | (P_typ (typ, pat)) -> let t = to_ms_typ ctx typ in
                          Pp_typ (convert_loc loc, t,(to_ms_pat ctx pat))
  | P_id (Id_aux (Id id,_)) ->
     Printf.eprintf "Got a P_id %s\n" id;
     Pp_id (convert_loc loc, (convert_to_isa id))
  | P_var ( P_aux ( P_id (Id_aux (Id id,_ )),_) , typ) ->
     Printf.eprintf "Got a P_var. Treating as id %s\n" id;
     Pp_id (convert_loc loc, (convert_to_isa id))
(*  | (P_app (Id_aux (Id id,_), [parg] )) -> let p = to_ms_pat ctx parg in
                                           Pp_app (convert_loc loc, id, p)*)
  | (P_app (Id_aux (Id id,_), pargs )) -> let ps = List.map (to_ms_pat ctx) pargs  in
                                          Printf.eprintf "to_ms_pat P_app %s\n" id;
                                          (Pp_app (convert_loc loc, (convert_to_isa id), ps))
(*  | (P_record (ps,b )) -> Pp_record(convert_loc loc ,
                                       List.map (fun (A.FP_aux (FP_Fpat (Id_aux(Id f, _),p),_)) -> (convert_to_isa f,to_ms_pat ctx p)) ps )*)
  | (P_vector pats ) -> let ps  = List.map (to_ms_pat ctx) pats  in
                              Pp_vector (convert_loc loc, ps)
  | (P_vector_concat pats) -> let ps  = List.map (to_ms_pat ctx) pats  in
                              Pp_vector_concat (convert_loc loc, ps)
  | (P_tup pats) -> let ps = List.map (to_ms_pat ctx) pats in
                    Pp_tup (convert_loc loc, ps)
  | (P_list ps ) -> Pp_list (convert_loc loc, List.map (fun x -> to_ms_pat ctx x) ps)
  | (P_cons (p1,p2) ) -> Pp_cons (convert_loc loc, to_ms_pat ctx p1, to_ms_pat ctx p2)
  | (P_string_append ps ) -> Pp_string_append (convert_loc loc, List.map (fun x -> to_ms_pat ctx x) ps)
                            

               
and to_ms_letbind ctx lb = match lb with
  | A.LB_aux (LB_val (pat, exp_e) , loc) ->
     (to_ms_pat ctx pat, to_ms_e ctx exp_e, loc, None)
(*     match pat with
       P_id (Id_aux (Id x,_))   -> (x , to_ms_e ctx exp_e,loc, None )
     | P_app (Id_aux (Id x, _),_) -> (x,to_ms_e ctx exp_e,loc,None )
     | P_typ (Typ_aux (Typ_id (Id_aux (Id id,_)),_), P_aux (P_id (Id_aux (Id x,_)),_)) -> (x,  to_ms_e ctx  exp_e, loc, Some id)
     | P_typ (Typ_aux (Typ_id (Id_aux (Id id,_)),_), P_aux (P_app (Id_aux (Id x, _),_) ,_)) ->
        (x,  to_ms_e ctx  exp_e, loc, Some id)
     | P_id _ | P_var _  | P_typ _ |  P_lit _ -> ("xxx" , to_ms_e ctx  exp_e, loc, None) (* FIXME NEed fresh xx *)
 *)
(*and convert_id (A.E_aux (E_id (Id_aux (Id x , _)),_)) = x*)

and convert_builtin ctx f elist loc = let e = Ep_tuple (Loc_unknown, List.map (fun (A.E_aux (exp,_) as exp_full) -> to_ms_e ctx exp_full ) elist) in
                                   Ep_app (Loc_unknown, VNamed (convert_to_isa f), e )

and convert_fexp_e ctx (loc : A.l) (A.FE_aux (FE_Fexp ( Id_aux (Id id,_) , E_aux( exp, _ ) ), _)) =  (convert_to_isa id , to_ms_e_aux ctx exp loc  )
                                         
(*and convert_fexp_e ctx (loc : A.l) (A.E_aux (exp, _)) = match exp with
   A.E_app_infix (E_aux (E_id (Id_aux (Id id, _ )),_), Id_aux (Id "=",_) , E_aux (arg2,_)) -> (convert_to_isa id , to_ms_e_aux ctx arg2 loc )*)

and convert_id_e ctx loc x = Ep_val (loc, V_var (x))

and to_ms_e ctx ((A.E_aux (exp,(loc,_))) : 'a A.exp ) : ep = to_ms_e_aux ctx exp loc           

and convert_lexp ctx (A.LEXP_aux (lexp, (loc1,_))) =
  let loc = convert_loc loc1 in
  match lexp with
    LEXP_cast (typ, x) -> ([ convert_id x ] , LEXPp_cast (loc, to_ms_typ ctx typ, (convert_id x)))
  | LEXP_id x -> ([ convert_id x ], LEXPp_mvar (loc, convert_id x))
  | LEXP_tup es -> let (mvars,lexps) = unzip (List.map (convert_lexp ctx) es) in
                   (List.concat mvars, LEXPp_tup (loc, lexps))
  | LEXP_field(lexp, Id_aux (Id id , _)) ->
     let (mvars, lexp) = convert_lexp ctx lexp in (mvars,LEXPp_field (loc, lexp, id))
  | LEXP_deref _ -> raise (NotSupported ("convert_lexp unhandled form - deref " ^ (pp_location loc1)))
  | LEXP_memory _ -> raise (Failure ("convert_lexp unhandled form - memory " ^ (pp_location loc1)))
  | LEXP_vector _ -> raise (Failure ("convert_lexp unhandled form - vec " ^ (pp_location loc1)))
  | LEXP_vector_concat _ -> raise (Failure ("convert_lexp unhandled form - vec c" ^ (pp_location loc1)))
  | LEXP_vector_range _ -> raise (Failure ("convert_lexp unhandled form - vec r " ^ (pp_location loc1)))
  (*  | LEXP_vector_concat es -> LEXP_vector_concat (loc, List.map (convert_lexp ctx) es)*)
                                                    


               
and  to_ms_e_aux ( ctx : 'a ctx ) ( exp : 'a A.exp_aux) ( loc : P.l )  = 
  let lc = convert_loc loc in
  match exp with
  | A.E_app (Id_aux (Id "add_int",_), [ E_aux (arg1,_); E_aux (arg2,_)]) ->  (Ep_bop (lc,Plus, to_ms_e_aux ctx arg1 loc,to_ms_e_aux ctx arg2 loc))
  | E_app (Id_aux (Id "add_range",_), [ E_aux (arg1,_); E_aux (arg2,_)]) ->
      (Ep_bop (lc,Plus , to_ms_e_aux ctx  arg1 loc, to_ms_e_aux ctx arg2 loc))
  | E_app (Id_aux (Id "leq_int",_), [ E_aux (arg1,_); E_aux (arg2,_)]) ->  (Ep_bop (lc,LEq, to_ms_e_aux ctx arg1 loc, to_ms_e_aux ctx arg2 loc))
  | E_app_infix (E_aux (e1,_), Id_aux (Id op,_), E_aux (e2,_)) -> Ep_app (lc,VNamed (convert_to_isa op), Ep_tuple (lc,[ to_ms_e_aux ctx e1 loc; to_ms_e_aux ctx e2 loc]))
  | E_app (Id_aux (Id f,_), [ E_aux (exp,_) ]) -> (Ep_app (lc, VNamed (convert_to_isa f), to_ms_e_aux ctx  exp loc))
  | E_app (Id_aux (Id f,_), e_list ) | E_app (Id_aux (Operator f,_), e_list ) -> let e = Ep_tuple (lc,List.map (fun (A.E_aux (exp,_)) -> to_ms_e_aux ctx exp loc) e_list) in
                                        Ep_app (lc,VNamed (convert_to_isa f), e )
  | E_tuple es  -> Ep_tuple (lc, List.map (to_ms_e ctx) es)
  | E_vector es -> Ep_vec (lc, List.map (to_ms_e ctx) es)
  | E_vector_append (e1,e2) -> convert_builtin ctx "vector_append" [e1;e2] loc
  | E_vector_access (e1,e2) -> convert_builtin ctx "vector_access" [e1;e2] loc
  | E_vector_subrange (e1,e2,e3) -> convert_builtin ctx "vector_subrange" [e1;e2;e3] loc
  | E_vector_update (e1,e2,e3) -> convert_builtin ctx "vector_update" [e1;e2;e3] loc
  | E_vector_update_subrange (e1,e2,e3,e4) -> convert_builtin ctx "vector_update" [e1;e2;e3;e4] loc
  | E_field ( A.E_aux(v,_) , Id_aux (Id id, loc)) -> Ep_proj (lc,convert_to_isa id, to_ms_e_aux ctx v loc )
  | E_record fexps -> Ep_record (lc, List.map (fun e -> convert_fexp_e ctx loc e ) fexps)
  | E_cast (typ,exp) -> Ep_cast (lc, to_ms_typ ctx typ, to_ms_e ctx exp)
  | E_list es -> Ep_list (lc, List.map (fun e -> to_ms_e ctx e ) es)
  | E_cons (e1,e2) -> Ep_cons (lc, to_ms_e ctx e1, to_ms_e ctx e2)
  | E_constraint ncons -> Ep_constraint(lc, to_ms_constraint ctx ncons)
  | E_sizeof nexp -> Ep_sizeof( lc, to_ms_ce ctx nexp)
  | E_record_update (e1,es) -> Ep_record_update(lc, to_ms_e ctx e1, List.map (convert_fexp_e ctx loc) es)
  | E_let (lb, exp_s ) -> let (pat,exp,loc,tid) = to_ms_letbind ctx lb in
                          Ep_let(lc, LBp_val (lc, pat, exp), to_ms_e ctx exp_s)
  | E_if ( (A.E_aux (e1,_)) , e2 ,e3 ) -> (Ep_if (lc,to_ms_e_aux ctx  e1 loc, to_ms_e ctx e2, to_ms_e ctx e3))
  | E_case (e,pexp_list) -> Ep_case (lc,to_ms_e ctx e , List.map (fun pexp -> to_ms_pexp ctx pexp) pexp_list)
  | E_assign ( lexp, e ) -> let (_, lexp ) = convert_lexp ctx lexp in
                            Ep_assign (lc, lexp , to_ms_e ctx e , Ep_val (lc,V_lit L_unit))
  | E_throw exp -> Ep_throw (lc,to_ms_e ctx exp)

(*  | E_assign (LEXP_aux (LEXP_cast (typ, x) , _), e2) ->
     Printf.eprintf "Assign with cast\n";
     E_assign_t ( lc, convert_id_e ctx lc (VNamed (convert_id x)), to_ms_typ ctx typ, to_ms_e ctx e2  )
           (* FIXME Can a stmt like thing appear on left of = ? *)
  | E_assign (LEXP_aux (LEXP_id x, _) ,e2) -> E_assign(lc, convert_id_e ctx lc (VNamed (convert_id x)), to_ms_e ctx e2)
  | E_assign _ -> raise (Failure ("to_ms_e_aux Unknown assign form " ^ (pp_location loc)))
 *)
                                    (*
  | E_assign (E_aux (E_id (Id_aux (Id x, _)), _) , e ) -> S_assign (lc,None, VNamed (convert_to_isa x) , to_ms_e ctx e  )
  | E_assign (E_aux (E_cast (typ, id) , _), e) -> 
     S_assign ( lc,Some (to_ms_typ ctx typ), VNamed (convert_to_isa (convert_id id)) , to_ms_e ctx e  )
  | E_assign ( E_aux (E_vector_access(e1,e2),_),e3) ->
     let e1 = to_ms_e ctx e1 in
     let e2 = to_ms_e ctx e2 in
     let e3 = to_ms_e ctx e3 in
     S_exp (convert_loc loc, E_app ( convert_loc loc, VNamed (convert_to_isa "vector_update"), E_tuple (convert_loc loc, [e1;e2;e3])))
  | E_assign (E_aux (E_app (Id_aux (Id f,_), e_list ),_),e) ->
              let e = Ep_tuple (lc,List.map (fun (A.E_aux (exp,_)) -> to_ms_e_aux ctx exp loc) (e_list @ [e])) in
              S_exp(lc,Ep_app (lc,VNamed (convert_to_isa f), e ))*)
  | E_block es -> convert_block ctx loc es 
  | E_loop ( While, _ , e1 , e2) -> Ep_loop(convert_loc loc, While , to_ms_e ctx e1, to_ms_e ctx e2)
  | E_loop ( Until, _ , e1 , e2) -> Ep_loop(convert_loc loc, Until , to_ms_e ctx e1, to_ms_e ctx e2)
  | E_for (Id_aux (Id lid,_), e1, e2 , e3 , inc_dec, e4 ) -> Ep_for(convert_loc loc,  (convert_to_isa lid),
                                                                   to_ms_e ctx e1, to_ms_e ctx e2, to_ms_e ctx e3,
                                                                   (match inc_dec with
                                                                     (A.Ord_aux (A.Ord_inc,_)) -> Ord_inc
                                                                   | (A.Ord_aux (A.Ord_dec,_)) -> Ord_dec),
                                                                   to_ms_e ctx e4)
  | E_return e -> Ep_return (convert_loc loc, to_ms_e ctx e)
  | E_exit e -> Ep_exit  (convert_loc loc, to_ms_e ctx e)
  | E_assert (e1,e2) -> Ep_assert( convert_loc loc, to_ms_e ctx e1, to_ms_e ctx e2)
  | E_id (Id_aux (Id x, loc)) -> if ESet.mem (convert_to_isa x) ctx.mvars then
                                   Ep_mvar (convert_loc loc, convert_to_isa x)
                                 else (Ep_val (lc,to_ms_v exp loc))
  | E_try (exp, pexps) -> Ep_try (convert_loc loc, to_ms_e ctx exp , List.map (to_ms_pexp ctx) pexps  )
  | _ -> (Ep_val (lc,to_ms_v exp loc))

                                                             



and to_ms_pexp ctx (Pat_aux (p,loc)) =
  match p with
    Pat_exp (pat,exp) -> PEXPp_exp( to_ms_pat ctx pat, to_ms_e ctx exp)
  | Pat_when (pat,exp1,exp2) -> PEXPp_exp ( to_ms_pat ctx pat, to_ms_e ctx exp1)
                                   
and check_record ctx es =
  Printf.eprintf "check_record\n";
  try 
    let fids_expr = List.map (fun (A.E_aux (E_app_infix (E_aux (E_id (Id_aux (Id fid,_)),_),  Id_aux (Id "=",_), E_aux (e,(loc,_))) , _ )) -> (convert_to_isa fid, to_ms_v e loc)) es
    in  Some (Ep_val (Loc_unknown,V_record (fids_expr)))
  with Match_failure _ -> None     

(*
and to_ms_eeq ctx ss = match ss with
    [s] -> to_ms_e ctx s
  | s::ss -> E_seq (Loc_unknown,to_ms_e ctx s, to_ms_eeq ctx ss)

and to_ms_eeq ctx ss = Ep_block (Loc_unknown, List.map (to_ms_e ctx) ss)
 *)

and add_mvars ctx mvars = { ctx with mvars = List.fold_left (fun mvars s -> ESet.add s mvars) ctx.mvars mvars }
                            
and  convert_block ( ctx : 'a ctx ) ( loc : A.l) (exps : ('a A.exp) list) : ep = match exps with
  | (A.E_aux (E_assign (lexp,e), (loc,_))) :: exps -> (match exps with
                                                         [] -> let (_, lexp) = convert_lexp ctx lexp in
                                                               Ep_assign (convert_loc loc, lexp , to_ms_e ctx e, Ep_val (convert_loc loc, V_lit L_unit))
                                                       | _ -> let (mvars,lexp) = convert_lexp ctx lexp in
                                                              let ctx' = add_mvars ctx mvars in 
                                                              Ep_assign (convert_loc loc, lexp, to_ms_e ctx e, convert_block ctx' loc exps))
  | exps -> Ep_block (convert_loc loc, List.map (to_ms_e ctx ) exps )

let to_ms_funcl_pexp ctx (A.Pat_aux (Pat_exp ( pat,exp), (loc,_))) = 
      let lc = convert_loc loc in 
      PEXPp_exp (to_ms_pat ctx pat, to_ms_e ctx exp)



(* FIXME Use filter_map or similar ?*)
let pick_some (xs : ('a option) list) : 'a option = List.fold_left (fun y x  -> match x with
                                                Some x -> Some x
                                               | None -> y) None xs            

let function_name funcl = match funcl with                                                                    
    (A.FCL_aux (FCL_Funcl (Id_aux (Id f,_), _),_)) -> f
  | (A.FCL_aux (FCL_Funcl (Id_aux (Operator f,_), _),_)) -> f

                                                              
let to_ms_funcl ctx funcl = match funcl with
    A.FCL_aux (A.FCL_Funcl ((Id_aux (_,_)), pexp ), (loc,_)) ->
       FCLp_funcl (convert_loc loc, convert_to_isa (function_name funcl), to_ms_funcl_pexp ctx pexp)


let to_ms_variant_typ name t : tau = let ls = TBindings.fold (fun k v l -> ( (convert_to_isa k,v)::l) ) t []
                             in T_refined_type (zvar,B_union (convert_to_isa name , ls), C_true) 

(* Convert pattern and also return its type; this is needed for functions with complex args ie
   where the top level pattern constructor is not P_typ
   We can't use this for all cases as ... *)
let rec to_ms_pat_and_typ ctx (A.P_aux (pat,(loc,_))) : tau * patp =
  let lc = convert_loc loc in
  match pat with    
  | (P_typ (typ, pat)) -> let t = to_ms_typ ctx typ in
                          (t, Pp_typ (lc,t,(to_ms_pat ctx pat)))
  | (P_tup pats) -> let (ts , ps ) = List.map (to_ms_pat_and_typ ctx) pats |> unzip in
                    let (bs,c) = normalise_tlist ts in 
                    (T_refined_type (zvar,B_tuple bs, c), Pp_tup (convert_loc loc, ps))                      
  | P_lit l  -> (T_refined_type (zvar,B_unit,C_true), Pp_lit (convert_loc loc, to_ms_lit l)) 
  | _ -> raise (Failure ("Unknown pat " ^ (pp_location loc)))
               
(*and to_ms_pat_raw ctx (A.P_aux (pat,loc)) = match pat with
    (P_app (Id_aux (Id id,_), [] )) -> P_id (convert_loc loc, VNamed (convert_to_isa id))
 *)

let args_pat_type ctx  (A.FCL_aux (FCL_Funcl (Id_aux (Id f,_) , pat ) , _ )) =
  if (FBindings.mem f ctx.funs ) then
    let (ks, b,c,tret) = FBindings.find f ctx.funs in
    let (A.Pat_aux (Pat_exp (pat,_),_)) = pat in
    let p = to_ms_pat ctx pat  in
    let t= T_refined_type (zvar,b , c ) in (t,p)
  else
    match pat with  (* Patterns in arg position are (sometimes?) of a form permitting inference of their type. See infer_funtyp in type_check.ml *)
      (Pat_aux (Pat_exp (P_aux (P_typ (typ,pat),_),_),_)) ->
       let t = to_ms_typ ctx typ in
       let p = to_ms_pat ctx pat in (t, p)
    | (Pat_aux (Pat_exp (pat, _),l)) -> let (t,p) = to_ms_pat_and_typ ctx pat in (t, p)


let args_pat_typ ctx  (A.FCL_aux (FCL_Funcl (Id_aux (Id f,_) , pat ) , _ )) =
  match pat with 
  | (Pat_aux (Pat_exp (P_aux (P_typ (typ,pat),_),_),_)) -> typ



                                                                                   
(* FIXME. This is a bit wrong as it will not catch end for variant/type that hasn't been introduced *)
let to_ms_end_scattered id ctx  =
  if ESet.mem id ctx.ended then
    None
  else
     let lc = Loc_unknown in
     match TBindings.find_opt id ctx.types with
       Some (CtxType (xbc,t,_,_)) ->
        PPrintEngine.ToChannel.compact stderr (string "Ending scattered type " ^^ pp_tp t);
        Some (DEFp_typedef (lc,convert_to_isa id, [], t)) (* FIXME. Not empty [] ? *)
     | None -> (match FBindings.find_opt id ctx.funs with
                | None -> None
                | Some (ks,b,c,ret) ->
                   let (_, cls ) = SBindings.find id ctx.scattereds  in
                   let cls = List.map (fun (c,e) -> let p = to_ms_pat ctx c in FCLp_funcl (lc,id, PEXPp_exp (p, to_ms_e ctx e))) cls in
                   Some (DEFp_fundef (lc, 
                                     A_function (xvar,b, c, ret ), cls))
               )

(* 
   Handle scattered forms. For unions we continue to use the ctx.types map and add to the list of variants for the type;
   for functions we used the ctx.scattereds map 
 *)

let is_union_sd sd  = match sd with
  | A.SD_variant _ -> true
  | A.SD_unioncl _ -> true
  | A.SD_end _ -> true
  | _ -> false

let is_fun_sd sd  = match sd with
  | A.SD_function _ -> true
  | A.SD_funcl _ -> true
  | A.SD_end _ -> true
  | _ -> false


(*
let to_ms_scattered_old ctx sd loc   = 
                                    match sd with
 |  (A.SD_function (rc,typ,eff, (Id_aux (Id id,_)))) ->
    (match convert_tannot ctx typ with
      Some (ctx,kids,t) ->  ( { ctx with scattereds = SBindings.add id (t, []) ctx.scattereds } ,None)
     | None -> (match FBindings.find_opt id ctx.funs with
                | Some ((_,_,_,t)) -> ( { ctx with scattereds = SBindings.add id (t,[]) ctx.scattereds } ,None)
                | None -> ( ctx, None ) (*raise (Failure "to_ms_scattered no type provided")*) ))
      
 | (SD_funcl (FCL_aux (FCL_Funcl (Id_aux (Id id,_),Pat_aux (Pat_exp (pat,expr), _)),_))) ->
    (match TBindings.find_opt id ctx.scattereds  with
    | Some (t, fcl ) ->
       ({ ctx with scattereds = SBindings.add id (t,fcl @ [(pat,expr)]) ctx.scattereds } , None)
    | None -> raise (Failure "to_ms_scattered not open"))
       
 | (SD_variant (Id_aux (Id id, _), typ_quant)) -> (* FIXME. Ignoring these extra bits *)
    let (ctx,typq) = to_ms_typquant ctx typ_quant in 
    let kvars= List.map (fun (x,y) -> x ) typq in (* FIXME SHould be taking types as well ??? *)
    let t = T_refined_type(zvar, B_union (convert_to_isa id, []), C_true) in
    Printf.eprintf "Addning scattered variant %s\n" id;
    ( { ctx with types = TBindings.add id  (typq,t) ctx.types } , None )
      
 | (SD_unioncl (Id_aux (Id id, _), type_union)) ->
    Printf.eprintf "Adding union cl %s %s \n" id (pp_location loc);
    (match TBindings.find_opt id ctx.types with
    | None -> raise (Failure "to_ms_scattered Union clause not opened")
    | Some  ((kvars,T_refined_type(kv, _ , B_union (isa_id, vs), c ))) -> 
       (match type_union with
          (A.Tu_aux (Tu_ty_id (t,Id_aux (Id ctor,_)),_)) -> let t = to_ms_typ ctx t
                                                            in ( { ctx with types = TBindings.add id ((kvars,T_refined_type(kv, zvar,B_union (isa_id, vs@[(convert_to_isa ctor, t)]), c))) ctx.types },None)))
                                                            
 | (SD_end (Id_aux (Id id,_))) ->
    (match to_ms_end_scattered id ctx with
    | None -> (ctx,None)
    | Some fd -> ( { ctx with ended = ESet.add id ctx.ended } ,Some fd))
 | SD_funcl _  -> raise (Failure ("to_ms_scattered SD_funcl unknown form " ^ (pp_location loc)))
 | SD_mapping _  -> raise (Failure ("to_ms_scattered SD_mapping " ^ (pp_location loc)))
 | SD_mapcl _  -> raise (Failure ("to_ms_scattered SD_mapcl " ^ (pp_location loc)))
 *)
           
let to_ms_scattered_aux ctx ( sd : 'a A.scattered_def_aux) loc   = 
                                    match sd with
 |  (A.SD_function (rc,typ,eff, (Id_aux (Id id,_)))) ->
    (match convert_tannot ctx typ with
       Some (ctx,kids,t) ->  (ctx,(SDp_function (convert_loc loc, Typ_annot_opt_psome_fn  (convert_loc loc, t) , convert_to_isa id)))
     | None ->  (ctx,(SDp_function (convert_loc loc, Typ_annot_opt_pnone (convert_loc loc) ,  convert_to_isa id))))
      
 | (SD_funcl (FCL_aux (FCL_Funcl (Id_aux (Id id,_),Pat_aux (Pat_exp (pat,expr), _)),_))) ->
    (ctx,(SDp_funclp (convert_loc loc, FCLp_funcl (convert_loc loc, convert_to_isa id, PEXPp_exp (to_ms_pat ctx pat, to_ms_e ctx expr)))))

 | SD_variant (Id_aux (Id id, _), typ_quant) -> 
    let (ctx,typq) = to_ms_typquant ctx typ_quant in
    let t = T_refined_type(zvar, B_union (convert_to_isa id, []), C_true) in
    Printf.eprintf "Adding scattered variant %s\n" id;
    let ctx = add_abbrev ctx id typq t [] []  in
    (ctx,SDp_variant (convert_loc loc, convert_to_isa id, typq))

 | (SD_unioncl (Id_aux (Id id, _), type_union)) ->
    Printf.eprintf "Adding union cl %s %s \n" id (pp_location loc);
    (match TBindings.find_opt id ctx.types with
    | None -> raise (Failure "to_ms_scattered Union clause not opened")
    | Some (CtxType (kvars,T_refined_type( _ , B_union (isa_id, vs), c ),_,_)) -> 
       (match type_union with
          (A.Tu_aux (Tu_ty_id (t,Id_aux (Id ctor,_)),_)) ->
             let t = to_ms_typ ctx t in 
             let ctx = add_abbrev ctx id kvars (T_refined_type(zvar,B_union (isa_id, vs@[(convert_to_isa ctor, t)]), c)) [] [] in
             (ctx,SDp_unioncl (convert_loc loc, convert_to_isa id, convert_to_isa ctor, t))))
    
 | (SD_end (Id_aux (Id id,_))) -> (ctx,(SDp_end (convert_loc loc, convert_to_isa id)))
           
 | SD_funcl _  -> raise (Failure ("to_ms_scattered SD_funcl unknown form " ^ (pp_location loc)))
 | SD_mapping _  -> raise (Failure ("to_ms_scattered SD_mapping " ^ (pp_location loc)))
 | SD_mapcl _  -> raise (Failure ("to_ms_scattered SD_mapcl " ^ (pp_location loc)))

let to_ms_scattered ctx ( sd : 'a A.scattered_def_aux) loc =
  try 
    let (ctx,sd) = to_ms_scattered_aux ctx sd loc
    in (ctx, Some (DEFp_scattered (convert_loc loc, sd)))
  with NotSupported s ->
    Printf.eprintf "Not supported (%s) \n" s;
    (ctx,None)


                                      
let to_ms_typedef ctx  (A.TD_aux (aux,(l,_)) : 'a A.type_def) =
  let lc = convert_loc l in 
  match aux with 
  | A.TD_variant (  Id_aux ((Id id), _ ), typq, typ_union , _) ->
     let (local_ctx, typq) = to_ms_typquant ctx typq in 
     let kvars= List.map (fun (x,y) -> x ) typq in (* FIXME SHould be taking types as well ??? *)
     let variant = List.fold_left (fun var x -> match x with
                                                  (A.Tu_aux (Tu_ty_id (t,Id_aux (Id id,_)),_)) -> TBindings.add id (to_ms_typ local_ctx t) var )
                     TBindings.empty typ_union in
     let variant = to_ms_variant_typ id variant                              
     in (add_abbrev ctx id typq variant [] []  , Some (DEFp_typedef (lc,convert_to_isa id,typq,variant))) 
          
  | A.TD_record ( Id_aux ((Id id), _ ), typq, id_typ_list, _) ->
     let (ctx,typq) = to_ms_typquant ctx typq in 
     let kvars= List.map (fun (x,y) -> x ) typq in (* FIXME SHould be taking types as well ??? *)    
     let fd_typ = List.map (fun (typ,A.Id_aux (Id id,_)) -> (convert_to_isa id, to_ms_typ ctx typ)) id_typ_list in
     let record = normalise_record_type fd_typ in
     let ctx = add_abbrev ctx id typq record [] [] in
     (ctx, Some (DEFp_typedef (lc,convert_to_isa id, typq, record )))
                                                              
  | A.TD_abbrev ( Id_aux (Id id, loc), tq , A_aux( A_typ typ, _)) -> (* FIXME Now has kind included. USe for what? *)
     Printf.eprintf "type abbrev %s loc=%s\n" (id) (pp_location loc);
     let (ctx,tq) = to_ms_typquant ctx tq in
     let (mods,ceks,_) = convert_invert_typ ctx (List.map (fun (VNamed k,(_,_)) -> k ) tq) (CE_val (V_var xvar) ) typ in
     let typ = to_ms_typ ctx typ in 
     let kvars = List.map (fun (x,y) -> x) tq in
     (add_abbrev ctx id tq typ mods ceks, Some (DEFp_typedef (lc, convert_to_isa id, tq,typ)))
       
  | A.TD_abbrev ( Id_aux (Id id, _), tq , A_aux( A_nexp nexp, _)) -> (* FIXME. Only assuming kind = Int *)
     Printf.eprintf "type abbrev kind %s\n" (id);
     let (ctx,tq) = to_ms_typquant ctx tq in
     let (mods,ceks,_) = ([],[],[]) in
     let ce = to_ms_ce ctx nexp in
     let kvars = List.map (fun (x,y) -> x) tq in
     (add_kind ctx id tq ce mods ceks, None )

       
  | A.TD_enum (Id_aux (Id id,_), id_list , _) ->
     let variant = List.fold_left (fun var x -> TBindings.add (up_id x) (to_ms_typ ctx (Typ_aux (Typ_id (mk_id "unit"),l ))) var) TBindings.empty id_list in
     let variant = to_ms_variant_typ id variant                              
     in (add_abbrev ctx id [] variant [] [] , Some (DEFp_typedef (lc, convert_to_isa id,[],variant)))

  | _  -> raise (Failure ("Unknown def type form: " ^ (pp_location l)))

                    
                                                               
(* This constructs the signature of the function taking into account constraints involving KID variables *)

(* FIXME. Reconstruct local context that includes type variables *)
let add_kids ctx loc kids = List.fold_left (fun ctx (VNamed x,(b,c)) ->
                            match b with
                            | B_int -> { ctx with kinds = KBindings.add x (A.K_aux (K_int, loc)) ctx.kinds }
                            | B_var _ -> { ctx with kinds = KBindings.add x (A.K_aux (K_type, loc)) ctx.kinds }
                            | B_bool -> { ctx with kinds = KBindings.add x (A.K_aux (K_order, loc)) ctx.kinds }) ctx kids
                
let to_ms_def_aux ctx d  =
  let lc = Loc_unknown in

  match d with
  (*    A.DEF_kind (KD_aux (_, (loc,_))) -> raise (Failure ("Kind def not supported" ^ (pp_location loc)))*)

  | A.DEF_type aux -> to_ms_typedef ctx aux

  | A.DEF_fundef (FD_aux ( FD_function (rc, _ , eff, (( funcl::_) as funcls)) ,(loc,_))) ->
     (*  | A.DEF_fundef (FD_aux ( FD_function (rc,Typ_annot_opt_aux(Typ_annot_opt_none,_), eff, (( funcl::_) as funcls)) ,(loc,_))) ->*)
     Printf.eprintf "to_ms_def DEF_fundef none %s\n" (pp_location loc);
     let fname = function_name funcl in
     let (local_ctx,kids, fun_t) = (match (FBindings.find_opt fname ctx.funs ) with
           | Some (kids,b,c,tret) -> (add_kids ctx loc kids ,kids, A_function(xvar,b,c,tret))
           | None ->  raise (Failure "to_ms_def DEF_fundef. Cannot find type for function")) in
     let funcls = List.map (to_ms_funcl local_ctx) funcls in
     (ctx, Some (DEFp_fundef  (convert_loc loc, fun_t ,funcls)))

(* Some confusion on why this needed. Sail TC seems put the correct type as a val spec so no need to try and work
it out here       
  | A.DEF_fundef (FD_aux ( FD_function (rc,Typ_annot_opt_aux(Typ_annot_opt_some (tq,typ_out),_), eff, (( funcl::_) as funcls)) ,(loc,_))) ->
     Printf.eprintf "to_ms_def DEF_fundef some %s\n" (pp_location loc);
     let (ctx,kids) = to_ms_typquant ctx tq in
     let args_pat_typ _ _ = typ_out in
     let typ_in = args_pat_typ ctx funcl in 
     let (b,c,tout,ceks) = to_ms_fun loc ctx kids typ_in typ_out in 
     let funcls = List.map (to_ms_funcl ctx) funcls in (* local_ctx might be needed - need to subst kids for ... *)
     let funcls = List.map (replace_ks_in_funcl ceks) funcls in
     (ctx, Some (DEFp_fundef  (convert_loc loc, A_function(xvar,b,c,tout),funcls)))
 *)
  | DEF_fundef _ -> raise (Failure "Unknown fundef form")
                          
  | DEF_mapdef _ -> (ctx,None) (* FIXME. Print warning ? *)
                         
  | DEF_val lb  ->
     let (pat,exp,(loc,_),_) = to_ms_letbind ctx lb in (ctx, Some (
                                                               (DEFp_val 
                                                                  (convert_loc loc, (LBp_val (convert_loc loc, pat , exp ))))))

  | DEF_overload ( fid ,fidlist) ->
     (ctx,Some (DEFp_overload (lc,convert_id fid,List.map convert_id fidlist)))
      
 | DEF_fixity _ -> (ctx,None)

 | DEF_spec (VS_aux (VS_val_spec (ts,Id_aux( id ,_) , _ ,_),(loc,_))) ->
    
    (try
      let id = (match id with Id x -> x | Operator x -> x) in
      let ((kids,b,c,t) as ftype) = to_ms_typschm ctx ts in 
      let ctx = { ctx with funs = FBindings.add id ftype ctx.funs } in
      (ctx, Some (DEFp_spec (convert_loc loc,  (convert_to_isa id),
                            A_function(xvar, b , c , t ))))
    with InvertFail -> 
          Printf.eprintf "Warning: Could not process DEF_spec at %s. Inversion failed\n" (pp_location loc);
          (ctx,None))

(*
 | DEF_spec (VS_aux (VS_val_spec (ts,Id_aux(DeIid id,_) , _ ,_),(loc,_))) -> (* fIXME *)
    let ((kids,b,c,t) as ftype) = to_ms_typschm ctx ts in 
    let ctx = { ctx with funs = FBindings.add  id ftype ctx.funs }  in
    (ctx, Some (DEFp_spec (convert_loc loc, (convert_to_isa id),
                          A_function(xvar, b , c , t ) 
                  )))
 *)                                                  
 | DEF_spec (VS_aux (_, (loc,_))) -> raise (Failure ("General DEF_spec not supported" ^ (pp_location loc)))
                       
 | DEF_default (DT_aux( DT_order (Ord_aux(Ord_inc,_)),loc)) -> (ctx,Some (DEFp_default (convert_loc loc, Ord_inc)))
 | DEF_default (DT_aux( DT_order (Ord_aux(Ord_dec,_)),loc)) -> (ctx,Some (DEFp_default (convert_loc loc, Ord_dec)))

 | DEF_scattered (SD_aux (sd, loc)) -> (ctx,None)
                      
 | DEF_reg_dec (DEC_aux (DEC_reg (_ , _ , typ, Id_aux (Id id, _)),(loc,_))) -> (ctx, Some (DEFp_reg (convert_loc loc,to_ms_typ ctx typ, VNamed (convert_to_isa id))))
 | DEF_reg_dec _ -> raise (Failure "Unknown reg_dec form")
                            
 | DEF_pragma (s1,s2,loc) -> raise (Failure ("Pragma def not supported " ^ (pp_location loc) ^ " " ^ s1 ^ " " ^ s2))
                                   
 | DEF_internal_mutrec _ -> raise (Failure "Mutrec not supported")

let to_ms_def ctx def =
  try
    to_ms_def_aux ctx def
  with NotSupported s ->
    Printf.eprintf "DEF form not supported (%s) \n" (Ast.show_def (fun fmt _ -> Format.pp_print_text fmt "(.)" ) def);
    (ctx,None)
                                  
let append_some xs x = match x with
  | Some x -> xs @ [x]
  | None -> xs
                               
           
let convert_ast ((A.Defs sail_defs) : 'a A.defs ) : progp =

  (* Process type defs first. Some may be scattered *)
  let (ctx,defs) = List.fold_left (fun (ctx,y) x ->
                              match x with
                              | A.DEF_type _ -> let (ctx,x) = to_ms_def ctx x in (ctx, append_some y x )
                              | A.DEF_scattered (SD_aux (sd,(loc,_))) when is_union_sd sd -> let (ctx,x) = to_ms_scattered ctx sd loc  in (ctx,append_some y x)
                              | _ -> (ctx,y))
                            (initial_ctx,[]) sail_defs in

  
  let (ctx,defs) = List.fold_left (fun (ctx,y) x ->
                              match x with
                              (*                              | A.DEF_type _ -> let (ctx,x) = to_ms_def ctx x in (ctx, append_some y x )*)
                              | A.DEF_scattered (SD_aux (sd,(loc,_))) when is_fun_sd sd -> let (ctx,x) = to_ms_scattered ctx sd loc  in (ctx,append_some y x)
                              | A.DEF_scattered (SD_aux (sd,(loc,_))) when is_union_sd sd -> let (_,x) = to_ms_scattered ctx sd loc  in (ctx,append_some y x) (* Why is this repeated? *)
                              | _ -> let (ctx,x) = to_ms_def ctx x in (ctx,append_some y x))
                            ( { initial_ctx with types = ctx.types; ended = ctx.ended },[]) sail_defs in
  
  let wlk = { visit_def = None; visit_b = Some (fun b -> match b with
                        B_tid s -> let CtxType (_,T_refined_type (_,b,c),_,_) = TBindings.find ( s) ctx.types
                                   in (c,b)
                      | _ -> (C_true,b))
            } in
  let defs = List.map (def_walk wlk) defs in
  Pp_prog defs
           

