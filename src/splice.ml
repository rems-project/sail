(* Currently limited to:
   - functions, no scattered, no preprocessor
   - no new undefined functions (but no explicit check here yet)
*)

open Ast
open Ast_util

let scan_defs (Defs defs) =
  let scan (ids, specs) = function
    | DEF_fundef fd ->
       IdSet.add (id_of_fundef fd) ids, specs
    | DEF_spec (VS_aux (VS_val_spec (_,id,_,_),_) as vs) ->
       ids, Bindings.add id vs specs
    | d -> raise (Reporting.err_general (def_loc d)
                    "Definition in splice file isn't a spec or function")
  in List.fold_left scan (IdSet.empty, Bindings.empty) defs

let filter_old_ast repl_ids repl_specs (Defs defs) =
  let check (rdefs,spec_found) def =
    match def with
    | DEF_fundef fd ->
       let id = id_of_fundef fd in
       if IdSet.mem id repl_ids
       then rdefs, spec_found
       else def::rdefs, spec_found
    | DEF_spec (VS_aux (VS_val_spec (_,id,_,_),_)) ->
       (match Bindings.find_opt id repl_specs with
        | Some vs -> DEF_spec vs :: rdefs, IdSet.add id spec_found
        | None -> def::rdefs, spec_found)
    | _ -> def::rdefs, spec_found
  in
  let rdefs, spec_found = List.fold_left check ([],IdSet.empty) defs in
  (List.rev rdefs, spec_found)

let filter_replacements spec_found (Defs defs) =
  let not_found = function
    | DEF_spec (VS_aux (VS_val_spec (_,id,_,_),_)) -> not (IdSet.mem id spec_found)
    | _ -> true
  in List.filter not_found defs

let splice env ast file =
  let parsed_ast = Process_file.parse_file file in
  let repl_ast = Initial_check.process_ast ~generate:false parsed_ast in
  let repl_ast = Rewrites.move_loop_measures repl_ast in
  let repl_ast = map_defs_annot (fun (l,_) -> l,Type_check.empty_tannot env) repl_ast in
  let repl_ids, repl_specs = scan_defs repl_ast in
  let defs1, specs_found = filter_old_ast repl_ids repl_specs ast in
  let defs2 = filter_replacements specs_found repl_ast in
  let new_ast = Defs (defs1 @ defs2) in
  Type_error.check Type_check.initial_env new_ast

