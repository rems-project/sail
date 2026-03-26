let read_lines filename =
  let in_chan = open_in filename in
  let rec loop acc =
    match input_line in_chan with
    | line -> loop (line :: acc)
    | exception End_of_file ->
        close_in in_chan;
        List.rev acc
  in
  loop []

let () =
  let mods = String.concat "\n" (List.map (fun l -> "  " ^ l) (read_lines "modules.txt")) in
  let stanza =
    [
      "(rocq.extraction";
      " (prelude SailExtraction)";
      Printf.sprintf " (extracted_modules\n%s)" mods;
      " (theories Stdlib Sail Ltac2 stdpp))";
    ]
  in
  List.iter print_endline stanza
