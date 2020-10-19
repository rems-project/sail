
let opt_files = ref ([] : string list)

let opt_taken = ref ([] : string list)
let opt_taken_list = ref ([] : string list)
let opt_all = ref "all_branches"

let opt_tab_width = ref 4

let opt_index = ref None
let opt_index_default = ref None
let opt_prefix = ref ""
                  
let opt_cumulative_table = ref None
let opt_histogram = ref false

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
        Arg.String (fun str -> opt_taken := str::!opt_taken),
        "<file> coverage information for branches taken while executing the model (default: sail_coverage)");
      ( "--taken",
        Arg.String (fun str -> opt_taken := str::!opt_taken),
        " long form of -t");
      ( "--taken-list",
        Arg.String (fun str -> opt_taken_list := str::!opt_taken_list),
        "<file> file containing a list of filenames of branches taken");
      ( "-a",
        Arg.String (fun str -> opt_all := str),
        "<file> information about all possible branches (default: all_branches)");
      ( "--all",
        Arg.String (fun str -> opt_all := str),
        " long form of -a");
      ( "--tab-width",
        Arg.Int (fun n -> opt_tab_width := n),
        "<integer> set the tab width for html output (default: 4)");
      ( "--index",
        Arg.String (fun str -> opt_index := Some str),
        "<name> create a <name>.html page as an index");
      ( "--index-default",
        Arg.String (fun str -> opt_index_default := Some str),
        "<file> The .sail file that will be displayed by the generated index page by default");
      ( "--prefix",
        Arg.String (fun str -> opt_prefix := str),
        "<string> Prepend a prefix to all generated html coverage files");
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
        "");
      ( "--cumulative-table",
        Arg.String (fun str -> opt_cumulative_table := Some str),
        "<file> write a table of cumulative coverage to file");
      ( "--histogram",
        Arg.Set opt_histogram,
        "display a histogram of the coverage level");
    ]

type span = {
    l1 : int;
    c1 : int;
    l2 : int;
    c2 : int;
  }

let string_of_span file span =
  Printf.sprintf "\"%s\" %d:%d - %d:%d" file span.l1 span.c1 span.l2 span.c2

module Span = struct
  type t = span
  let compare s1 s2 = compare s1 s2
end

module SpanSet = Set.Make(Span)
module SpanMap = Map.Make(Span)

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

let add_span spans _ file l1 c1 l2 c2 =
  StringMap.update (Filename.basename file)
    (fun x ->
      let file_spans = Option.value x ~default:SpanMap.empty in
      Some (SpanMap.update { l1 = l1; c1 = c1; l2 = l2; c2 = c2 }
              (function None -> Some 1 | Some i -> Some (i+1)) file_spans))
    spans

let read_more_coverage filename spans = 
  let spans = ref spans in
  let chan = open_in filename in
  try
    let rec loop () =
      let line = input_line chan in
      spans := Scanf.sscanf line "%c %S, %d, %d, %d, %d" (add_span !spans);
      loop ()
    in
    loop ()
  with End_of_file ->
    close_in chan;
    !spans

let read_coverage filename = read_more_coverage filename StringMap.empty

(** We color the source either red (bad) or green (good) if it's
   covered vs uncovered. If we have nested uncovered branches, they
   will be increasingly bad, whereas nested covered branches will be
   increasingly good. *) 
type source_char = {
    mutable badness : int;
    mutable goodness : int;
    mutable bad_zero_width: bool;
    char : char;
  }

let zero_width span = span.l1 = span.l2 && span.c1 = span.c2

let mark_bad_region source span _ =
  if zero_width span then (
    source.(span.l2 - 1).(span.c2 - 1).bad_zero_width <- true
  ) else (
    source.(span.l1 - 1).(span.c1).badness <- source.(span.l1 - 1).(span.c1).badness + 1;
    source.(span.l2 - 1).(span.c2 - 1).badness <- source.(span.l2 - 1).(span.c2 - 1).badness - 1
  )

let mark_good_region source span _ =
  if not (zero_width span) then (
    source.(span.l1 - 1).(span.c1).goodness <- source.(span.l1 - 1).(span.c1).goodness + 1;
    source.(span.l2 - 1).(span.c2 - 1).goodness <- source.(span.l2 - 1).(span.c2 - 1).goodness - 1
  )
    
let process_line l = Array.init (String.length l) (fun n -> { badness = 0; goodness = 0; char = l.[n]; bad_zero_width = false })

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

let file_info file all taken =
  let diff span all_count taken_count =
    match all_count, taken_count with
    | Some _, Some _ -> None
    | Some n, None   -> Some n
    | None, Some _ -> begin
        Printf.eprintf "Warning: span not in all branches file: %s\n" (string_of_span file span);
        None
      end
    | None, None -> None
  in
  let not_taken = SpanMap.merge diff all taken in
  
  let percent =
    if SpanMap.cardinal all != 0 then
      let p = 100. *. (Float.of_int (SpanMap.cardinal taken) /. Float.of_int (SpanMap.cardinal all)) in
      Printf.sprintf "%.0f%%" p
    else
      "-"
  in

  taken,
  not_taken,
  Printf.sprintf "%s (%d/%d) %s" (Filename.basename file) (SpanMap.cardinal taken) (SpanMap.cardinal all) percent

let index_css = "
body, html {
  width: 100%;
  height: 100%;
  margin: 0;
  padding: 0;
}

table {
  width: 100%;
  height: 100%;
  margin: 0;
  padding: 0;
  border-collapse: collapse;
  overflow: hidden;
}

.left {
  width: 20%;
}

.left .scroll {
  height: 100vh;
  overflow-x: hidden;
  overflow-y: auto;
}

.right {
  width: 80%;
}

td {
  padding: 0;
  margin: 0;
}

tr {
  padding: 0;
  margin: 0;
  height: 100%;
  overflow-x: hidden;
  overflow-y: auto;
}

iframe {
  height: 100%;
  width: 100%;
  display: block;
  margin: 0;
  padding: 0;
}
"

let html_file_for file =
  !opt_prefix ^ Filename.remove_extension (Filename.basename file) ^ ".html"
              
let read_taken_files () =
  match !opt_cumulative_table with
  | Some table_name ->
     let table_chan = open_out table_name in
     List.iter (fun src_file -> Printf.fprintf table_chan "%s, " (Filename.basename src_file)) !opt_files;
     Printf.fprintf table_chan ",, Total\n";
     let read_more filename spans =
       let new_spans = read_more_coverage filename spans in
       let counts = List.map (fun src_name ->
           let taken = Option.value ~default:SpanMap.empty (StringMap.find_opt (Filename.basename src_name) new_spans) in
           SpanMap.cardinal taken
         ) !opt_files
       in
       List.iter (fun i -> Printf.fprintf table_chan "%d, " i) counts;
       Printf.fprintf table_chan ",, %d\n" (List.fold_left (+) 0 counts);
       new_spans
     in
     let spans = List.fold_right read_more !opt_taken StringMap.empty in
     close_out table_chan;
     spans
  | None ->
     List.fold_right read_more_coverage !opt_taken StringMap.empty

let get_file_spans filename all taken =
      let file = Filename.basename filename in
      let all = match StringMap.find_opt file all with
        | None -> Printf.eprintf "Warning: %s not found in coverage files\n" file; SpanMap.empty
        | Some s -> s
      in
      let taken = Option.value ~default:SpanMap.empty (StringMap.find_opt file taken) in
      all, taken

let main () =
  let all = read_coverage !opt_all in
  let taken = read_taken_files () in
  List.iter (fun file ->
      let all, taken = get_file_spans file all taken in
      let taken, not_taken, desc = file_info file all taken in
      print_endline desc;

      if !opt_histogram && not (SpanMap.is_empty taken) then begin
          let histogram = SpanMap.fold (fun _ count m -> IntMap.update count (function None -> Some 1 | Some i -> Some (i+1)) m) taken IntMap.empty in
          Printf.printf "Count | Number of spans\n";
          IntMap.iter (fun count spans ->
              Printf.printf "%5d | %7d\n" count spans
            ) histogram
        end;
      
      let source = read_source file in
      SpanMap.iter (mark_good_region source) taken;
      SpanMap.iter (mark_bad_region source) not_taken;
      
      let output_file = html_file_for file in
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
      output_string chan (Printf.sprintf "<h1>%s</h1>\n" desc);
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

              if loc.bad_zero_width then (
                output_string chan (Printf.sprintf "<span style=\"background-color: %s\">" (bad_color ()));
                output_string chan "&#171;Invisible branch not taken here&#187";
                output_string chan "</span>"
              );
              
              assert (!current_goodness >= 0);
              assert (!current_badness >= 0)
              
            ) line;
          output_string chan "<br>\n"
        ) source;

      output_string chan "</code>\n";
      output_string chan "</body>\n";
      output_string chan "</html>";
      
      close_out chan
    ) !opt_files;

  begin match !opt_index with
  | Some name ->
     let chan = open_out (name ^ ".html") in
     
     output_string chan "<!DOCTYPE html>\n";
     output_string chan "<html lang=\"en\">\n";
     Printf.ksprintf (output_string chan)
       "<head>\n<meta charset=\"utf-8\">\n<title>Coverage Report</title>\n<style>%s</style>\n</head>\n"
       index_css;
     output_string chan "<body>\n";
     
     output_string chan "<table><tr><td class=\"left\"><div class=\"scroll\">";
     List.iter (fun file ->
         let all, taken = get_file_spans file all taken in
         let _, _, desc = file_info file all taken in
         Printf.ksprintf (output_string chan) "<a href=\"%s\" target=\"source\">%s</a><br>\n"
           (html_file_for file) desc
       ) !opt_files;
     output_string chan "</div></td>";

     output_string chan "<td class=\"right\">";
     begin match !opt_index_default with
     | Some default_file ->
        Printf.ksprintf (output_string chan) "<iframe src=\"%s\" name=\"source\"></iframe>"
          (html_file_for default_file);
     | None ->
        output_string chan "<iframe name=\"source\"></iframe>"
     end;
     output_string chan "</td></tr></table>\n";
     output_string chan "</body>\n";
     output_string chan "</html>";
     close_out chan
  | None -> ()
  end

let usage_msg = "usage: sailcov -t <file> -a <file> <.sail files>\n"

let read_taken_lists () =
  List.iter (fun filename ->
      let chan = open_in filename in
      try
        let rec loop () =
          opt_taken := (input_line chan)::!opt_taken;
          loop ()
        in loop ()
      with End_of_file ->
        ()) !opt_taken_list

let _ =
  Arg.parse options
    (fun s -> opt_files := !opt_files @ [s])
    usage_msg;
  read_taken_lists ();
  begin opt_taken := match !opt_taken with
  | [] -> ["sail_coverage"]
  | l -> List.rev l
  end;
  try main () with
  | Sys_error msg -> prerr_endline msg; exit 1 
