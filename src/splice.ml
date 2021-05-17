(* Currently limited to:
   - functions, no scattered, no preprocessor
   - no new undefined functions (but no explicit check here yet)
*)

open Ast
open Ast_defs
open Ast_util

let scan_ast { defs; _ } =
  let scan (ids, specs) = function
    | DEF_fundef fd ->
       IdSet.add (id_of_fundef fd) ids, specs
    | DEF_spec (VS_aux (VS_val_spec (_,id,_,_),_) as vs) ->
       ids, Bindings.add id vs specs
    | DEF_pragma (("file_start" | "file_end"), _ ,_) ->
       ids, specs
    | d -> raise (Reporting.err_general (def_loc d)
                    "Definition in splice file isn't a spec or function")
  in List.fold_left scan (IdSet.empty, Bindings.empty) defs

let filter_old_ast repl_ids repl_specs { defs; _ } =
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

let filter_replacements spec_found { defs; _ } =
  let not_found = function
    | DEF_spec (VS_aux (VS_val_spec (_,id,_,_),_)) -> not (IdSet.mem id spec_found)
    | _ -> true
  in List.filter not_found defs

let splice ast file =
  let parsed_ast = Process_file.parse_file file |> snd in
  let repl_ast = Initial_check.process_ast ~generate:false (Parse_ast.Defs [(file, parsed_ast)]) in
  let repl_ast = Rewrites.move_loop_measures repl_ast in
  let repl_ast = map_ast_annot (fun (l,_) -> l,Type_check.empty_tannot) repl_ast in
  let repl_ids, repl_specs = scan_ast repl_ast in
  let defs1, specs_found = filter_old_ast repl_ids repl_specs ast in
  let defs2 = filter_replacements specs_found repl_ast in
  Type_error.check Type_check.initial_env { ast with defs = defs1 @ defs2 }

