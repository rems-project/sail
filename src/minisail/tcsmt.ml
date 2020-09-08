module A = Ast
module I = Minisail_isa.SailAST
module E = Minisail_isa.Env


let rec convert_nc = function
  | _  -> A.NC_aux (A.NC_true,Unknown)


(* We use Type_check.prove_smt by cooking up an env with just the constraints *)
let prove ncs nc =
  Printf.eprintf "smt prover\n";
  let ncs' = List.map convert_nc ncs in
  let env = List.fold_left (fun x y -> Type_check.Env.add_constraint y x) Type_check.initial_env ncs' in
  Type_check.prove_smt env (convert_nc nc)
              
               
