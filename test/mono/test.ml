match Out.run() with
| Done _ -> exit 0
| Fail s -> prerr_endline ("Fail: " ^ s); exit 1
| Error s -> prerr_endline ("Error: " ^ s); exit 1
| _ -> prerr_endline "Unexpected outcome"; exit 1
