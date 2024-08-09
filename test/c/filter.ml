match input_char stdin with
| '"' -> ()
| _ -> exit 1
;;

while true do
  match input_char stdin with
  | '"' -> begin
    match input_char stdin with
    | '"' -> output_char stdout '\"'
    | '\n' ->
      begin match input_char stdin with
        | exception End_of_file -> exit 0
        | _ -> exit 1
      end
    | exception End_of_file -> exit 0
    | _ -> exit 1
  end
  | c -> output_char stdout c
done
;;
