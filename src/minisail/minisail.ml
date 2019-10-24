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
                       | ITD.OK () -> Printf.printf "Found ok derivation"; Set.bot_set (*Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
                       | Error _ -> Printf.printf "Found error\n" ; Set.bot_set)
  (*     Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
    | Empty -> Set.bot_set
and set_of_pred_limit i _A  (Seq f) =
  Printf.eprintf "i=%d\n" i;
  (match f () with
     Predicate.Empty -> Set.bot_set
   | Insert (x, p) -> (match x with
                       | ITD.OK () -> Printf.printf "Found ok derivation"; Set.bot_set (*Set.insert _A x (set_of_pred_limit (i-1) _A p)*)
                       | Error _ -> Printf.printf "Found error\n" ; Set.bot_set)
      | Join (p, xq) -> Set.sup_set _A (set_of_pred_limit (i-1) _A p) (set_of_seq_limit (i-1) _A xq));;


              
(*open Minisailplusdecl_core
module AST=Minisailplusdecl_ast.SyntaxPED
module IT = Minisailplusdecl_core.TypingMonadFunction
 *)


let opt_dmsp_check_before = ref None
let opt_dmsp_check_after = ref None

let check_prog_decl ms_ast =
  let (Msp_ast.Set.Set res) = set_of_pred_limit 10000
             {equal=fun x y -> (x == y)} (ITD.check_prog_i_o ms_ast) in 
  match res with
    [] -> Printf.eprintf "Program didn't type check.\n"
  |  (_) :: xs ->  Printf.eprintf "Program type checked. (%d derivations)\n" (List.length res)

let check_prog_fn ms_ast =
    match (fst (Msp_ast.Monad.run_state (ITF.check_p_emptyEnv ms_ast) (StateD (Msp_ast.Arith.zero_int,[])))) with
     | Msp_ast.Monad.Check_Ok _ -> Printf.eprintf  "Checking with function. ok\n"; exit 0;
     | Check_Fail (_, r) -> Printf.eprintf "Checking with function. Failed ";
                            PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
                            exit 1

let check_def_fn t p g def i = 
    match (Msp_ast.Monad.run_state (ITF.check_def t p g  def) (StateD (i,[]))) with
     | (Msp_ast.Monad.Check_Ok (t',(p',g')),StateD (i',_)) -> Printf.eprintf  "CHECK DEF: ok\n"; (t',p',g',i')
     | (Check_Fail (_, r), StateD (i',_)) ->
        Printf.eprintf "CHECK DEF: failed. ";
        PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
        PPrintEngine.ToChannel.compact stderr ((pp_raw_defp def) ^^ string "\n");
                            (t,p,g,i')
                                 

let rec check_defs_fn t p g defs i = match defs with
    [] -> (t,p,g,i)
  | (def::defs) -> let (t,p,g,i) = check_def_fn t p g def i 
                   in check_defs_fn t p g defs i

let check_prog_defs_fn (AST.Pp_prog defs) = check_defs_fn Ctx.emptyTEnv Ctx.emptyPiEnv Msp_ast.TypingUtils.emptyEnv defs (Msp_ast.Arith.zero_int)
                              
let check_ast (vrb : int)  (sail_ast : 'a A.defs) : unit =
  let ms_ast = convert_ast sail_ast in
    (match vrb with
       | 0 -> ()
       | 1 -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_progp ms_ast) ^^ (string "\n"))
       | _ -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_raw_progp ms_ast) ^^ (string "\n")));
    (*    check_prog_fn ms_ast*)
   let _ = check_prog_defs_fn ms_ast in
   ()
     
(*    check_prog_decl ms_ast;*)
(*
  match (fst (Minisailplus_ast.Monad.run_state (IT.check_p_emptyEnv ms_ast) (StateD (Minisailplus_ast.Arith.zero_int,[])))) with
     | Minisailplus_ast.Monad.Check_Ok _ -> Printf.eprintf  "Checking with function. ok\n"; exit 0;
     | Check_Fail (_, r) -> Printf.eprintf "Checking with function. Failed ";
                            PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
                            exit 1
 *)
    


    
