let tests = [
  "test1", Test1.defs;
  "test2", Test2.defs;
] ;;

let run_all () = List.iter Run_interp.run tests ;;

run_all () ;;
