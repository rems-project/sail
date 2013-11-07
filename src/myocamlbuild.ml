open Ocamlbuild_plugin ;;
open Command ;;
open Pathname ;;
open Outcome ;;

(* paths relative to _build *)
let lem_dir = "../../../lem" ;;
let lem_libdir = lem_dir / "ocaml-lib/_build" ;;
let lem_lib = lem_libdir / "extract" ;;
let lem = lem_dir / "lem" ;;

(* Order matters - respect dependencies! *)
let lem_deps = List.map ((/) "lem_interp") [
  "interp_ast.lem";
  "interp.lem";
  "interp_lib.lem";
  ] ;;
let lem_opts = List.fold_right (fun s l -> [A "-i"; P s] @ l) lem_deps [] ;;

dispatch begin function
| After_rules ->
    (* ocaml_lib "lem_interp/interp"; *)
    ocaml_lib ~extern:true ~dir:lem_libdir  ~tag_name:"use_lem" lem_lib;

    rule "lem -> ml"
    ~prod: "%.ml"
    ~deps: ("%.lem" :: lem_deps)
    (fun env builder -> Seq [
      Cmd (S ([ P lem] @ lem_opts @ [ A "-ocaml"; P (env "%.lem") ]));
      mv (basename (env "%.ml")) (dirname (env "%.ml"))
      ]);

    rule "sail -> lem"
    ~prod: "%.lem"
    ~deps: ["%.sail"; "main.native"]
    (fun env builder -> Seq [
      Cmd (S [ P "./main.native"; A "-lem_ast"; P (env "%.sail") ]);
      mv (basename (env "%.lem")) (dirname (env "%.lem"))
      ]);

| _ -> ()
end ;;
