open Big_int

open Error

let acquire_char_list (fname : string) =
  let char_list = ref [] in
  try
    let ic = open_in_bin fname in
    while true do
      let c = input_char ic in
      let _ = char_list := c :: !char_list in
        ()
    done;
    let _ = close_in ic in
    Fail "acquire_char_list: the impossible happened"
  with End_of_file ->
    Success (List.rev !char_list)
;;

let serialise_char_list (fname : string) bytes =
  let rec go oc bytes =
    match bytes with
      | []    -> ()
      | x::xs -> output_char oc x; go oc xs
  in
    try
      let oc = open_out_bin fname in
      let _  = go oc bytes in
      let _  = close_out oc in
        Success ()
    with _ ->
      Fail "serialise_char_list: unable to open file for writing"
;;