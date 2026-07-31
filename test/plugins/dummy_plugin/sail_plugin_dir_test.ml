open Libsail

(* Exists only for regression test in test/plugins/run_tests.py
   Provides a plugin adding a marker that can never appear
   unless this plugin was loaded. *)
let _ =
  Target.register ~name:"plugin_dir_test"
    ~options:
      [
        ( Flag.create "sail_plugin_dir_test_marker",
          Arg.Unit (fun () -> ()),
          "marker option for the SAIL_PLUGIN_DIR test"
        );
      ]
    Target.empty_action
