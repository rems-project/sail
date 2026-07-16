open Libsail
open Helpers

open Ast_util

module TestScanner = Ast_util.Scanner (struct
  type t = Sail_file.position

  type category = unit

  let subloc p l =
    let open Sail_file.Position in
    match Reporting.simp_loc l with
    | None -> false
    | Some (p1, p2) ->
        let same_file = Sail_file.handle_compare p1.pos_fname p2.pos_fname = 0 in
        same_file
        &&
        let in_line_range = p1.pos_lnum <= p.pos_lnum && p.pos_lnum <= p2.pos_lnum in
        let in_char_range = p1.pos_cnum <= p.pos_cnum && p.pos_cnum <= p2.pos_cnum in
        in_line_range && in_char_range

  let categorize_exp _ = None
  let categorize_lexp _ = None
  let categorize_pat _ = None
end)

let scanner_tests =
  let case name contents line character expected =
    Alcotest.test_case name `Quick (fun () ->
        Parmap.toplevel_handler (fun () ->
            let handle = handle_of contents in
            let path = Sail_file.to_path handle in
            let _, _, ast, _, _ =
              Frontend.load_paths ~default_sail_dir:Filename.current_dir_name [] Type_check.initial_env
                [Corelib_sail.path; path]
            in
            let p = Option.get (Sail_file.lexing_position handle { line; character }) in
            let _, tannot, _ = Option.get (TestScanner.find_annot_ast p ast) in
            let typ = Type_check.typ_of_tannot tannot in
            Alcotest.(check string) name expected (string_of_typ typ)
        )
    )
  in
  List.mapi
    (fun i (contents, line, character, typ) -> case ("Scanner " ^ string_of_int i) contents line character typ)
    [
      ("function f() -> int =\n2\n", 1, 0, "int(2)");
      ("function f() -> int = {\n2\n}\n", 1, 0, "int(2)");
      ("function f() -> int = {\nlet x : int =\n3;\nx\n}\n", 2, 0, "int(3)");
      ("function f() -> int = {\nlet x = 3;\nlet x = 4;\nx\n}\n", 3, 0, "int(4)");
    ]

let suites : unit Alcotest.test list = [("Ast_util.Scanner", scanner_tests)]
