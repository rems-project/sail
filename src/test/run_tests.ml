let tests = [
  "test1", Test1.defs;
  "test2", Test2.defs;
  "test3", Test3.defs;
  "vectors", Vectors.defs;
] ;;

let run_all () = List.iter Run_interp.run tests ;;

run_all () ;;
