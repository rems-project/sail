open Convert_ast
open PPrintEngine
open PPrintCombinators
open Pp_fail

open Minisailplus_pp
open Msp_ast
       
module AST=Msp_ast.SyntaxPED
module ITD = Msp_decl_fail_typing.TypingDeclFailRules
module ITF = Msp_fn_typing.TypingMonadFunction
module Ctx = Msp_ast.ContextsPiDelta

let rec set_of_seq_limit i _A
  = function
    Predicate.Join (p, xq) -> Set.sup_set _A (set_of_pred_limit (i-1) _A p) (set_of_seq_limit (i-1) _A xq)
  | Insert (x, p) ->
     (match x with
                       | ITD.OK  -> Printf.eprintf "Found ok derivation"; Set.bot_set (*Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
                       | Error _ -> Printf.eprintf "Found error\n" ; Set.bot_set)
  (*     Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
    | Empty -> Set.bot_set
and set_of_pred_limit i _A  (Seq f) =
  Printf.eprintf "i=%d\n" i;
  (match f () with
     Predicate.Empty -> Set.bot_set
   | Insert (x, p) -> (match x with
                       | ITD.OK  -> Printf.eprintf "Found ok derivation"; Set.bot_set (*Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
                       | Error _ -> Printf.eprintf "Found error\n" ; Set.bot_set)
      | Join (p, xq) -> Set.sup_set _A (set_of_pred_limit (i-1) _A p) (set_of_seq_limit (i-1) _A xq));;


              
(*open Minisailplusdecl_core
module AST=Minisailplusdecl_ast.SyntaxPED
module IT = Minisailplusdecl_core.TypingMonadFunction
 *)


let opt_dmsp_check_before = ref None
let opt_dmsp_check_after = ref None

let pp_ok_error ok = match ok with
    ITD.OK -> string "Ok\n"
  | Error (ITD.CheckFail (s, loc)) -> string "Error: " ^^ string s ^^ string " loc=" ^^ (pp_loc loc)

let rec pp_trace_check_def = function
                           | ITD.CheckFunDef w -> string "CheckFunDef " ^^ separate (string ", ") (List.map  pp_trace_pexp w) ^^ string ")"
                           | _ -> string "check_def_w"  
and pp_trace_pexp = function
                  | CheckPExp (pat,ep) -> string "CheckPexp (" ^^ pp_trace_ep ep ^^ string ")"
                  | _ -> string "check_pexp_w"
and pp_trace_ep = function
                | CheckSubtype (ep,st) -> string "CheckSubType (" ^^ pp_trace_infer_ep ep ^^ string ", " ^^ pp_subtype st ^^ string ")"
                | _ -> string "check_ep_w"
and pp_trace_infer_ep = function
  | InferApp (ep,st) -> string "InferApp (" ^^ pp_trace_infer_ep ep ^^ string ", " ^^ pp_subtype st ^^ string ")"
  | InferVal v -> string "InferVal (" ^^ pp_trace_infer_v v ^^ string ")"
  | InferTuple _ -> string "InferTuple"
and pp_trace_infer_v = function
  | InferVVar _ ->  string "InferVar"
  | _ -> string "infer_v_w"
and pp_subtype = function
  | Subtype _ -> string "subtype_w ok"
  | SubtypeFail -> string "subtype_w fail"
                                    
let check_prog_decl ms_ast =
(*  let (Msp_ast.Set.Set res) = set_of_pred_limit 10
             {equal=fun x y -> (x == y)} (ITD.check_prog_i_o ms_ast) in *)
  let (Msp_ast.Set.Set res) = Predicate.set_of_pred
             {equal=fun x y -> (x == y)} (ITD.check_prog_i_o_o_o ms_ast) in
  match res with
    [] -> Printf.eprintf "Program didn't type check.\n"
  |  (_,(_,ok)) :: xs ->  Printf.eprintf "Program type checked. (%d derivations) " (List.length res);
                    PPrintEngine.ToChannel.compact stderr ((pp_ok_error ok) ^^ string "\n")

let loc_def = function
  | AST.DEFp_fundef ((loc,_), _, _ ) -> loc
  | DEFp_typedef ((loc,_),_, _, _) -> loc
  | DEFp_spec ((loc,_), _ , _ ) -> loc
  | DEFp_val ((loc,_) , _ ) -> loc
  | _ -> (Msp_ast.Location.Loc_unknown)
           (*
    DEFp_reg of Location.loc * SyntaxVCT.tau * SyntaxVCT.xp |
    DEFp_overload of Location.loc * string * string list |
    DEFp_scattered of Location.loc * scattered_defp |
    DEFp_default of Location.loc * SyntaxVCT.order
            *)

let some_head xs = match xs with
    [] -> None
  | x::xs -> Some x

(* Get one of the successful derivations *)
let get_ok res = 
  let res = List.filter (fun (t, (p , (g, (i, (k,(l,ok)))))) -> match ok with
                                                             ITD.OK  -> true
                                                           | _ -> false) res in
  some_head res

                  
let get_error res =
  match get_ok res with
    Some _ -> None
  | None -> some_head res

    
           
let check_def_decl i t p g def =
  let _ = Printf.eprintf "++ Checking def term:\n" ;  PPrintEngine.ToChannel.compact stderr (pp_defp def) in
  let _ = Printf.eprintf "\n" in
  (let (Msp_ast.Set.Set res) = Predicate.set_of_pred
             {equal=fun x y -> (x == y)} (ITD.check_def_i_i_i_i_i_o_o_o_o_o_o_o i t p g def) in
  match res with
    [] -> Printf.eprintf "Failed. No derivations. Loc=";
          PPrintEngine.ToChannel.compact stderr (pp_loc (loc_def def) );
          Printf.eprintf "\n\n";
          Some (i,t,p,g,false)
  |  xs -> match get_error xs with
             Some (_,(_,(_,(_,(_,(tr,err)))))) -> Printf.eprintf "Failed. %d derivations\n" (List.length res);
                                         PPrintEngine.ToChannel.compact stderr ((pp_ok_error err) );
                                         Printf.eprintf "\n\n";
                                         Some (i,t,p,g,false)
           | None -> Printf.eprintf "Success. %d derivations\n\n" (List.length res);
                     let Some (t,(p,(g,(_,(i,(tr,_)))))) = get_ok res in
                     PPrintEngine.ToChannel.compact stderr (pp_trace_check_def tr);
                     Printf.eprintf "\n";
                     Some (i,t,p,g,true)

  )

let check_prog_fn ms_ast =
    match (fst (Msp_ast.Monad.run_state (ITF.check_p_emptyEnv ms_ast) (StateD (Msp_ast.Arith.zero_int,[])))) with
     | Msp_ast.Monad.Check_Ok _ -> Printf.eprintf  "Checking with function. ok\n"; exit 0;
     | Check_Fail (_, r) -> Printf.eprintf "Checking with function. Failed ";
                            PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
                            exit 1

let check_def_fn t p g def i = 
    match (Msp_ast.Monad.run_state (ITF.check_def t p g  def) (StateD (i,[]))) with
     | (Msp_ast.Monad.Check_Ok (t',(p',g')),StateD (i',_)) -> Printf.eprintf  "Success.\n"; (t',p',g',i')
     | (Check_Fail (_, r), StateD (i',_)) ->
        Printf.eprintf "CHECK DEF: failed. ";
        PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
        PPrintEngine.ToChannel.compact stderr ((pp_raw_defp def) ^^ string "\n");
                            (t,p,g,i')
                                 

let rec check_defs_fn t p g defs i = match defs with
    [] -> (t,p,g,i)
  | (def::defs) -> let (t,p,g,i) = check_def_fn t p g def i 
                   in check_defs_fn t p g defs i

let rec check_defs_decl i t p g defs = match defs with
    [] -> (i,t,p,g,true)
  | (def::defs) -> match check_def_decl i t p g def with
                     Some (i,t,p,g,ok) -> let(i,t,p,g,ok2) = check_defs_decl i t p g defs in (i,t,p,g,ok & ok2)
                   | None -> (i,t,p,g,false)

                                    
let check_prog_defs_fn (AST.Pp_prog (_ ,defs)) = check_defs_fn Msp_ast.TypingUtils.emptyTEnv
                                                   Ctx.emptyPiEnv Msp_ast.TypingUtils.emptyEnv defs (Msp_ast.Arith.zero_int)

let check_prog_defs_decl (AST.Pp_prog (_, defs)) =
  let (_,_,_,_,ok) = check_defs_decl (Msp_ast.Arith.zero_nat) Msp_ast.TypingUtils.emptyTEnv Ctx.emptyPiEnv Msp_ast.TypingUtils.emptyEnv defs
  in ok
                              
let check_ast (vrb : int)  (sail_ast : 'a A.defs) : unit =
  let ms_ast = convert_ast sail_ast in
    (match vrb with
       | 0 -> ()
       | 1 -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_progp ms_ast) ^^ (string "\n"))
       | _ -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_raw_progp ms_ast) ^^ (string "\n")));
    (*    check_prog_fn ms_ast*)
    (*   let _ = check_prog_defs_fn ms_ast in*)
    if check_prog_defs_decl ms_ast then
      exit 0
    else
      exit 1
                            
(*
  match (fst (Minisailplus_ast.Monad.run_state (IT.check_p_emptyEnv ms_ast) (StateD (Minisailplus_ast.Arith.zero_int,[])))) with
     | Minisailplus_ast.Monad.Check_Ok _ -> Printf.eprintf  "Checking with function. ok\n"; exit 0;
     | Check_Fail (_, r) -> Printf.eprintf "Checking with function. Failed ";
                            PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
                            exit 1
 *)
    


    
