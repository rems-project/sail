open Ocamlbuild_plugin ;;
open Command ;;
open Pathname ;;
open Outcome ;;

let split ch s =
  let x = ref [] in
  let rec go s =
    if not (String.contains s ch) then List.rev (s :: !x)
    else begin
      let pos = String.index s ch in
      x := (String.before s pos)::!x;
      go (String.after s (pos + 1))
    end
  in
  go s

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

(* New library magic: *)
let lem_opts = [A "-lib"; P "../lem_interp"] ;;

dispatch begin function
| After_rules ->
    (* ocaml_lib "lem_interp/interp"; *)
    ocaml_lib ~extern:true ~dir:lem_libdir  ~tag_name:"use_lem" lem_lib;

    rule "lem -> ml"
    ~prod: "%.ml"
    ~dep: "%.lem"
    (fun env builder -> Seq [
      Cmd (S ([ P lem] @ lem_opts @ [ A "-ocaml"; P (env "%.lem") ]));
      ]);

    rule "sail -> lem"
    ~prod: "%.lem"
    ~deps: ["%.sail"; "main.native"]
    (fun env builder ->
      let sail_opts = List.map (fun s -> A s) (
        "-lem_ast" ::
        try
          split ',' (Sys.getenv "SAIL_OPTS")
        with Not_found -> []) in
      Seq [
        Cmd (S ([ P "./main.native"] @ sail_opts @ [P (env "%.sail")]));
        mv (basename (env "%.lem")) (dirname (env "%.lem"))
      ]);

| _ -> ()
end ;;
