open Convert_ast
open Minisailplus_pp
open Minisailplus_core
open PPrintEngine
open PPrintCombinators
open Pp_fail
       
module AST=Minisailplus_ast.SyntaxPED
module IT = Minisailplus_core.TypingMonadFunction
                    


let opt_dmsp_check = ref None
                         
let check_ast vrb sail_ast =
  let ms_ast = convert_ast sail_ast in
    (match vrb with
       | 0 -> ()
       | 1 -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_progp ms_ast) ^^ (string "\n"))
       | _ -> PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_raw_progp ms_ast) ^^ (string "\n")));

  match (fst (Minisailplus_ast.Monad.run_state (IT.check_p_emptyEnv ms_ast) (StateD (Minisailplus_ast.Arith.zero_int,[])))) with
     | Minisailplus_ast.Monad.Check_Ok _ -> Printf.eprintf  "Checking with function. ok\n"; exit 0;
     | Check_Fail (_, r) -> Printf.eprintf "Checking with function. Failed ";
                            PPrintEngine.ToChannel.compact stderr ((pp_fail r) ^^ string "\n");
                            exit 1



           

