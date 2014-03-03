open Printf

let tests = [
  "test1", Test1.defs;
  "test2", Test2.defs;
  "test3", Test3.defs;
  "pattern", Pattern.defs;
  "vectors", Vectors.defs;
  "regbits", Regbits.defs;
  (*"power", Power.defs;*)
] ;;

let run_one ((name, _) as t) = (name, Run_interp.run t)

let run_all () =
  let results = List.map run_one tests in
  if List.for_all (fun (_, r) -> r) results then
    eprintf "\nSUCCESS: all tests passed!\n"
  else begin
    eprintf "\nFAILURE: the following tests failed:\n";
    List.iter (fun (name, r) -> if not r then eprintf "- %s\n" name) results;
    exit 1
  end
;;

run_all () ;;
