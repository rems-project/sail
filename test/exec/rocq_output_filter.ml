match input_char stdin with '"' -> () | _ -> exit 1;;

while true do
  match input_char stdin with
  | '"' -> (
      match input_char stdin with
      | '"' -> output_char stdout '\"'
      | '\n' -> (
          match input_char stdin with exception End_of_file -> exit 0 | _ -> exit 1
        )
      | exception End_of_file -> exit 0
      | _ -> exit 1
    )
  | c -> output_char stdout c
done
