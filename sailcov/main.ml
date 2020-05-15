
let opt_files = ref ([] : string list)

let opt_taken = ref "sail_coverage"

let opt_all = ref "all_branches"

let opt_tab_width = ref 4

type color = {
    hue: int;
    saturation: int;
  }

let opt_bad_color = ref { hue = 0; saturation = 85 }
let opt_good_color = ref { hue = 120; saturation = 85 }
let opt_darken = ref 5
                   
let clamp_degree n = max 0 (min n 360)
let clamp_percent n = max 0 (min n 100)

let use_alt_colors () = 
  opt_good_color := { !opt_good_color with hue = 220 };
  opt_bad_color := { !opt_good_color with hue = 50 }

let options =
  Arg.align [
      ( "-t",
        Arg.String (fun str -> opt_taken := str),
        "<file> coverage information for branches taken while executing the model (default: sail_coverage)");
      ( "-a",
        Arg.String (fun str -> opt_all := str),
        "<file> information about all possible branches (default: all_branches)");
      ( "--tab-width",
        Arg.Int (fun n -> opt_tab_width := n),
        "<integer> set the tab width for html output (default: 4)");
      ( "--covered-hue",
        Arg.Int (fun n -> opt_good_color := { !opt_good_color with hue = clamp_degree n }),
        "<int> set the hue (between 0 and 360) of the color used for code that is covered (default: 120 (green))");
      ( "--uncovered-hue",
        Arg.Int (fun n -> opt_bad_color := { !opt_bad_color with hue = clamp_degree n }),
        "<int> set the hue (between 0 and 360) of the color used for code that is not covered (default: 0 (red))");
      ( "--covered-saturation",
        Arg.Int (fun n -> opt_good_color := { !opt_good_color with saturation = clamp_percent n }),
        "<int> set the saturation (between 0 and 100) of the color used for code that is covered (default: 85)");
      ( "--uncovered-saturation",
        Arg.Int (fun n -> opt_bad_color := { !opt_bad_color with saturation = clamp_percent n }),
        "<int> set the hue (between 0 and 100) of the color used for code that is not covered (default: 85)");
      ( "--nesting-darkness",
        Arg.Int (fun n -> opt_darken := n),
        "<int> factor which controls how much darker nested spans of the same color become (default: 5)");
      ( "--alt-colors",
        Arg.Unit use_alt_colors,
        " swap default colors from red/green into alternate yellow/blue theme");
      ( "--alt-colours",
        Arg.Unit use_alt_colors,
        "")
    ]

type span = {
    file : string;
    l1 : int;
    c1 : int;
    l2 : int;
    c2 : int;
  }

module Span = struct
  type t = span
  let compare s1 s2 = compare s1 s2
end

module SpanSet = Set.Make(Span)
module SpanMap = Map.Make(Span)

let mk_span _ file l1 c1 l2 c2 = { file = Filename.basename file; l1 = l1; c1 = c1; l2 = l2; c2 = c2 }
               
let read_coverage filename = 
  let spans = ref SpanSet.empty in
  let chan = open_in filename in
  try
    let rec loop () =
      let line = input_line chan in
      spans := SpanSet.add (Scanf.sscanf line "%c %S, %d, %d, %d, %d" mk_span) !spans;
      loop ()
    in
    loop ()
  with End_of_file ->
    close_in chan;
    !spans

(** We color the source either red (bad) or green (good) if it's
   covered vs uncovered. If we have nested uncovered branches, they
   will be increasingly bad, whereas nested covered branches will be
   increasingly good. *) 
type source_char = {
    mutable badness : int;
    mutable goodness : int;
    char : char;
  }

let mark_bad_region source span =
  source.(span.l1 - 1).(span.c1).badness <- source.(span.l1 - 1).(span.c1).badness + 1;
  source.(span.l2 - 1).(span.c2 - 1).badness <- source.(span.l2 - 1).(span.c2 - 1).badness - 1

let mark_good_region source span =
  source.(span.l1 - 1).(span.c1).goodness <- source.(span.l1 - 1).(span.c1).goodness + 1;
  source.(span.l2 - 1).(span.c2 - 1).goodness <- source.(span.l2 - 1).(span.c2 - 1).goodness - 1
  
let process_line l = Array.init (String.length l) (fun n -> { badness = 0; goodness = 0; char = l.[n] })

let read_source filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    let rec loop () =
      lines := process_line (input_line chan) :: !lines;
      loop ()
    in
    loop ()
  with End_of_file ->
    close_in chan;
    Array.of_list (List.rev !lines)

let output_html_char chan c =
  if c == ' ' then
    output_string chan "&nbsp;"
  else if c == '<' then
    output_string chan "&lt;"
  else if c == '>' then
    output_string chan "&gt;"
  else if c == '"' then
    output_string chan "&quot;"
  else if c == '\t' then
    output_string chan (String.concat "" (List.init !opt_tab_width (fun _ -> "&nbsp;")))
  else
    output_char chan c
    
let main () =
  let all = read_coverage !opt_all in
  let taken = read_coverage !opt_taken in
  List.iter (fun file ->
      let all = SpanSet.filter (fun s -> s.file = Filename.basename file) all in
      let taken = SpanSet.filter (fun s -> s.file = Filename.basename file) taken in
      let not_taken = SpanSet.diff all taken in

      let source = read_source file in
      SpanSet.iter (mark_good_region source) taken;
      SpanSet.iter (mark_bad_region source) not_taken;

      let output_file = Filename.remove_extension (Filename.basename file) ^ ".html" in
      let chan = open_out output_file in

      let current_goodness = ref 0 in
      let current_badness = ref 0 in

      let clamp_lightness l = max 30 (min 80 l) in

      let html_color color darkness =
        Printf.sprintf "hsl(%d, %d%%, %d%%)"
          color.hue color.saturation (clamp_lightness ((80 + !opt_darken) - darkness * !opt_darken))
      in
      let good_color () = html_color !opt_good_color !current_goodness in
      let bad_color () = html_color !opt_bad_color !current_badness in

      output_string chan "<!DOCTYPE html>\n";
      output_string chan "<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n";
      output_string chan (Printf.sprintf "<title>%s</title>" (Filename.remove_extension (Filename.basename file)));
      output_string chan "</head>\n";
      output_string chan "<body>\n";
      output_string chan "<code style=\"display: block\">\n";

      Array.iter (fun line ->
          Array.iter (fun loc ->
              if loc.goodness < 0 && loc.badness < 0 then (
                output_html_char chan loc.char;
                current_goodness := !current_goodness + loc.goodness;
                current_badness := !current_badness + loc.badness;
                for _ = 1 to abs loc.goodness + abs loc.badness do
                  output_string chan (Printf.sprintf "</span>")
                done
              ) else if loc.goodness < 0 then (
                assert (loc.badness >= 0);
                output_html_char chan loc.char;
                current_goodness := !current_goodness + loc.goodness;
                for _ = 1 to abs loc.goodness do
                  output_string chan (Printf.sprintf "</span>")
                done
              ) else if loc.badness < 0 then (
                assert (loc.goodness >= 0);
                output_html_char chan loc.char;
                current_badness := !current_badness + loc.badness;
                for _ = 1 to abs loc.badness do
                  output_string chan (Printf.sprintf "</span>")
                done
              ) else if loc.badness > 0 then (
                assert (loc.goodness <= 0);
                current_badness := !current_badness + loc.badness;
                for _ = 1 to loc.badness do
                  output_string chan (Printf.sprintf "<span style=\"background-color: %s\">" (bad_color ()));
                done;
                output_html_char chan loc.char
              ) else if loc.goodness > 0 then (
                assert (!current_badness == 0);
                current_goodness := !current_goodness + loc.goodness;
                for _ = 1 to loc.goodness do
                  output_string chan (Printf.sprintf "<span style=\"background-color: %s\">" (good_color ()));
                done;
                output_html_char chan loc.char
              ) else (
                output_html_char chan loc.char
              );
              assert (!current_goodness >= 0);
              assert (!current_badness >= 0)
                      
            ) line;
          output_string chan "<br>\n"
        ) source;

      output_string chan "</code>\n";
      output_string chan "</body>\n";
      output_string chan "</html>";
      
      close_out chan;
      Printf.printf "%s (%d/%d)\n" file (SpanSet.cardinal taken) (SpanSet.cardinal all)
    ) !opt_files

let usage_msg = "usage: sailcov -c <file> -a <file> <.sail files>\n"

let _ =
  Arg.parse options
    (fun s -> opt_files := !opt_files @ [s])
    usage_msg;
  try main () with
  | Sys_error msg -> prerr_endline msg; exit 1 
