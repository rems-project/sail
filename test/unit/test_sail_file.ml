(* Unit tests for the public Sail_file interface.

   To keep the tests hermetic they build file handles with
   [add_virtual_file], which does not touch the filesystem, rather
   than [editor_take_file], which canonicalises paths with realpath
   and hence needs a real file on disk.

   The [suites] value at the bottom is collected by the [test_libsail] runner. *)

open Libsail
open Helpers

(* -- Sail_file.contents round-trips the initial file ---------------------- *)

let contents_tests =
  let roundtrip name input () =
    let handle = handle_of input in
    Alcotest.(check string) name input (Sail_file.contents handle)
  in
  [
    Alcotest.test_case "single line" `Quick (roundtrip "single line" "default Order dec");
    Alcotest.test_case "trailing newline" `Quick (roundtrip "trailing newline" "a\nb\n");
    Alcotest.test_case "no trailing newline" `Quick (roundtrip "no trailing newline" "a\nb");
    Alcotest.test_case "empty" `Quick (roundtrip "empty" "");
  ]

(* -- Sail_file.lexing_position (UTF-16 -> byte conversion) ---------------- *)

(* Editor positions carry UTF-16 code-unit character offsets; Sail lexing
   positions carry byte offsets. With no pending edits, [lexing_position] just
   converts the offset against the addressed line, so we can use it to exercise
   the UTF-16 -> byte conversion through the public API. The multi-byte
   characters used below (given as explicit UTF-8 byte escapes) are:
     beta   U+03B2  "\xce\xb2"          2 bytes, 1 UTF-16 unit
     approx U+2248  "\xe2\x89\x88"      3 bytes, 1 UTF-16 unit
     grin   U+1F600 "\xf0\x9f\x98\x80"  4 bytes, 2 UTF-16 units (surrogate pair) *)

(* Byte offset within its line of the editor position [(line, utf16)]. *)
let byte_offset handle line utf16 =
  match Sail_file.lexing_position handle (pos line utf16) with
  | Some p -> p.pos_cnum - p.pos_bol
  | None -> Alcotest.failf "lexing_position returned None for (%d, %d)" line utf16

let lexing_position_tests =
  let case name ?(line = 0) contents utf16 expected =
    Alcotest.test_case name `Quick (fun () ->
        let handle = handle_of contents in
        Alcotest.(check int) name expected (byte_offset handle line utf16)
    )
  in
  [
    (* Plain ASCII: UTF-16 offset equals the byte offset. *)
    case "ascii start" "hello" 0 0;
    case "ascii middle" "hello" 3 3;
    case "ascii end" "hello" 5 5;
    case "ascii past end clamps to byte length" "hello" 99 5;
    (* Two-byte character: "a<beta>c". *)
    case "two-byte: before" "a\xce\xb2c" 1 1;
    case "two-byte: after" "a\xce\xb2c" 2 3;
    case "two-byte: end" "a\xce\xb2c" 3 4;
    (* Three-byte character: "a<approx>c". *)
    case "three-byte: before" "a\xe2\x89\x88c" 1 1;
    case "three-byte: after" "a\xe2\x89\x88c" 2 4;
    case "three-byte: end" "a\xe2\x89\x88c" 3 5;
    (* Four-byte (astral) character counts as two UTF-16 units: "a<grin>b". *)
    case "astral: before" "a\xf0\x9f\x98\x80b" 1 1;
    case "astral: after (2 units)" "a\xf0\x9f\x98\x80b" 3 5;
    case "astral: end" "a\xf0\x9f\x98\x80b" 4 6;
    (* Offsets are per-line, and the byte offset is relative to the line. *)
    case "second line" ~line:1 "aa\nb\xce\xb2b" 2 3;
  ]

(* -- Sail_file.edit_file / apply_edits ----------------------------------- *)

(* Apply a batch of edits (each [(start, end, text)]) to [contents] and check
   the resulting buffer. Character offsets are UTF-16 code units (what the LSP
   handler stores); [apply_edits] resolves them to byte offsets against the
   lines being edited. Edits in a batch are applied in order, each relative to
   the state produced by the previous. *)
let apply_case name contents edits expected =
  Alcotest.test_case name `Quick (fun () ->
      let handle = handle_of contents in
      List.iter (fun (s, e, text) -> Sail_file.edit_file handle (edit s e text)) edits;
      Sail_file.apply_edits handle;
      Alcotest.(check string) name expected (Sail_file.contents handle)
  )

let apply_edits_tests =
  [
    apply_case "insert single character" "hello world" [(pos 0 5, pos 0 5, ",")] "hello, world";
    apply_case "delete a range" "abcdef" [(pos 0 1, pos 0 4, "")] "aef";
    apply_case "replace within a line" "abcdef" [(pos 0 1, pos 0 4, "XYZ")] "aXYZef";
    apply_case "insert splits a line" "abcd" [(pos 0 2, pos 0 2, "\n")] "ab\ncd";
    apply_case "prepend a whole line" "first\nsecond" [(pos 0 0, pos 0 0, "// header\n")] "// header\nfirst\nsecond";
    apply_case "delete across lines joins them" "one\ntwo" [(pos 0 3, pos 1 0, "")] "onetwo";
    apply_case "multi-line replacement" "one\ntwo\nthree" [(pos 0 1, pos 2 2, "X\nY\nZ")] "oX\nY\nZree";
    apply_case "append at end of file" "abc\n" [(pos 1 0, pos 1 0, "def")] "abc\ndef";
    (* Second edit's offsets refer to the buffer after the first edit. *)
    apply_case "sequential edits in one batch" "abc" [(pos 0 0, pos 0 0, "X"); (pos 0 4, pos 0 4, "Y")] "XabcY";
    (* An empty queue leaves the buffer untouched. *)
    apply_case "no pending edits" "unchanged" [] "unchanged";
    (* Offsets are UTF-16 code units, so they must be resolved against the
       multi-byte contents. "a<beta>c" has units a=0, beta=1, c=2. *)
    apply_case "insert after a two-byte char" "a\xce\xb2c" [(pos 0 2, pos 0 2, "X")] "a\xce\xb2Xc";
    apply_case "delete a two-byte char" "a\xce\xb2c" [(pos 0 1, pos 0 2, "")] "ac";
    (* "a<grin>b" spans units a=0, grin=1..2 (surrogate pair), b=3. *)
    apply_case "insert after an astral char" "a\xf0\x9f\x98\x80b" [(pos 0 3, pos 0 3, "X")] "a\xf0\x9f\x98\x80Xb";
    apply_case "replace an astral char" "a\xf0\x9f\x98\x80b" [(pos 0 1, pos 0 3, "Y")] "aYb";
  ]

(* apply_edits should clear the queue, so applying twice is not the same as
   applying an edit twice. *)
let idempotence_tests =
  [
    Alcotest.test_case "apply_edits clears the queue" `Quick (fun () ->
        let handle = handle_of "abc" in
        Sail_file.edit_file handle (edit (pos 0 0) (pos 0 0) "X");
        Sail_file.apply_edits handle;

        Sail_file.apply_edits handle;
        Alcotest.(check string) "second apply is a no-op" "Xabc" (Sail_file.contents handle)
    );
  ]

let suites : unit Alcotest.test list =
  [
    ("Sail_file.contents", contents_tests);
    ("Sail_file.lexing_position", lexing_position_tests);
    ("Sail_file.apply_edits", apply_edits_tests @ idempotence_tests);
  ]
