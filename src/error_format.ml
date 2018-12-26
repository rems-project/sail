
let rec skip_lines in_chan = function
  | n when n <= 0 -> ()
  | n -> ignore (input_line in_chan); skip_lines in_chan (n - 1)

let rec read_lines in_chan = function
  | n when n <= 0 -> []
  | n ->
     let l = input_line in_chan in
     let ls = read_lines in_chan (n - 1) in
     l :: ls

type formatter = {
    indent : string;
    endline : string -> unit;
    loc_color : string -> string
  }

let err_formatter = {
    indent = "";
    endline = prerr_endline;
    loc_color = Util.red
  }

let buffer_formatter b = {
    indent = "";
    endline = (fun str -> Buffer.add_string b (str ^ "\n"));
    loc_color = Util.red
  }

let format_endline str ppf = ppf.endline (ppf.indent ^ (Str.global_replace (Str.regexp_string "\n") ("\n" ^ ppf.indent) str))

let underline_single color cnum_from cnum_to =
  if (cnum_from + 1) >= cnum_to then
    Util.(String.make cnum_from ' ' ^ clear (color "^"))
  else
    Util.(String.make cnum_from ' ' ^ clear (color ("^" ^ String.make (cnum_to - cnum_from - 2) '-' ^ "^")))

let format_code_single' fname in_chan lnum cnum_from cnum_to contents ppf =
  skip_lines in_chan (lnum - 1);
  let line = input_line in_chan in
  let line_prefix = string_of_int lnum ^ Util.(clear (cyan " |")) in
  let blank_prefix = String.make (String.length (string_of_int lnum)) ' ' ^ Util.(clear (ppf.loc_color " |")) in
  format_endline (Printf.sprintf "[%s]:%d:%d-%d" Util.(fname |> cyan |> clear) lnum cnum_from cnum_to) ppf;
  format_endline (line_prefix ^ line) ppf;
  format_endline (blank_prefix ^ underline_single ppf.loc_color cnum_from cnum_to) ppf;
  contents { ppf with indent = blank_prefix ^ " " }

let underline_double_from color cnum_from eol =
  Util.(String.make cnum_from ' ' ^ clear (color ("^" ^ String.make (eol - cnum_from - 1) '-')))

let underline_double_to color cnum_to =
  Util.(clear (color (String.make (cnum_to - 1) '-' ^ "^")))

let format_code_double' fname in_chan lnum_from cnum_from lnum_to cnum_to contents ppf =
  skip_lines in_chan (lnum_from - 1);
  let line_from = input_line in_chan in
  skip_lines in_chan (lnum_to - lnum_from - 1);
  let line_to = input_line in_chan in
  let line_to_prefix = string_of_int lnum_to ^ Util.(clear (cyan " |")) in
  let line_from_padding = String.make (String.length (string_of_int lnum_to) - String.length (string_of_int lnum_from)) ' ' in
  let line_from_prefix = string_of_int lnum_from ^ line_from_padding ^ Util.(clear (cyan " |")) in
  let blank_prefix = String.make (String.length (string_of_int lnum_to)) ' ' ^ Util.(clear (ppf.loc_color " |")) in
  format_endline (Printf.sprintf "[%s]:%d:%d-%d:%d" Util.(fname |> cyan |> clear) lnum_from cnum_from lnum_to cnum_to) ppf;
  format_endline (line_from_prefix ^ line_from) ppf;
  format_endline (blank_prefix ^ underline_double_from ppf.loc_color cnum_from (String.length line_from)) ppf;
  format_endline (line_to_prefix ^ line_to) ppf;
  format_endline (blank_prefix ^ underline_double_to ppf.loc_color cnum_to) ppf;
  contents { ppf with indent = blank_prefix ^ " " }

let format_code_single fname lnum cnum_from cnum_to contents ppf =
  try
    let in_chan = open_in fname in
    begin
      try format_code_single' fname in_chan lnum cnum_from cnum_to contents ppf
      with
      | _ -> close_in_noerr in_chan; ()
    end
  with
  | _ -> ()

let format_code_double fname lnum_from cnum_from lnum_to cnum_to contents ppf =
  try
    let in_chan = open_in fname in
    begin
      try format_code_double' fname in_chan lnum_from cnum_from lnum_to cnum_to contents ppf
      with
      | _ -> close_in_noerr in_chan; ()
    end
  with
  | _ -> ()

let format_pos p1 p2 contents ppf =
  let open Lexing in
  if p1.pos_lnum == p2.pos_lnum
  then format_code_single p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) (p2.pos_cnum - p2.pos_bol) contents ppf
  else format_code_double p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol) contents ppf

let rec format_loc l contents =
  match l with
  | Parse_ast.Unknown -> contents
  | Parse_ast.Range (p1, p2) -> format_pos p1 p2 contents
  | Parse_ast.Unique (_, l) -> format_loc l contents
  | Parse_ast.Documented (_, l) -> format_loc l contents
  | Parse_ast.Generated l ->
     fun ppf -> (format_endline "Code generated nearby:" ppf; format_loc l contents ppf)

type message =
  | Location of Parse_ast.l * message
  | Line of string
  | List of (string * message) list
  | Seq of message list
  | With of (formatter -> formatter) * message

let bullet = Util.(clear (blue "*"))

let rec format_message msg =
  match msg with
  | Location (l, msg) ->
     format_loc l (format_message msg)
  | Line str ->
     format_endline str
  | Seq messages ->
     fun ppf -> List.iter (fun msg -> format_message msg ppf) messages
  | List list ->
     let format_list_item ppf (header, msg) =
       format_endline (Util.(clear (blue "*")) ^ " " ^ header) ppf;
       format_message msg { ppf with indent = ppf.indent ^ "   " }
     in
     fun ppf -> List.iter (format_list_item ppf) list
  | With (f, msg) -> fun ppf -> format_message msg (f ppf)
