(* Entry point for the libsail unit tests.

   Each Libsail file under test has its own [test_<file>] module exposing a
   [suites] value (a list of named Alcotest suites). Collect them all here so a
   single run covers the whole library. To test a new file, add a
   [test_<file>.ml] module and append its [suites] below. *)

let () = Alcotest.run "libsail" (List.concat [Test_sail_file.suites])
