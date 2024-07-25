(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_defs

module Highlight = struct
  type t = Id | Keyword | Kind | Comment | String | Pragma | Internal | Operator | Literal | TyVar

  let to_class = function
    | Id -> "sail-id"
    | Keyword -> "sail-keyword"
    | Kind -> "sail-kind"
    | Comment -> "sail-comment"
    | String -> "sail-string"
    | Pragma -> "sail-pragma"
    | Internal -> "sail-internal"
    | Operator -> "sail-operator"
    | Literal -> "sail-literal"
    | TyVar -> "sail-ty-var"
end

let highlights ~filename ~contents =
  let lexbuf = Initial_check.get_lexbuf_from_string ~filename ~contents in
  let comments = ref [] in
  let highlights = Queue.create () in
  let mark h = Queue.add (h, lexbuf.lex_start_p.pos_cnum, lexbuf.lex_curr_p.pos_cnum) highlights in
  let rec go () =
    let open Parser in
    match Lexer.token comments lexbuf with
    | Eof -> ()
    | Id _ ->
        mark Highlight.Id;
        go ()
    | Int | Bool | TYPE | Order ->
        mark Highlight.Kind;
        go ()
    | String _ ->
        mark Highlight.String;
        go ()
    | Doc _ ->
        mark Highlight.Comment;
        go ()
    | And | As | Assert | By | Match | Clause | Dec | Op | Default | Effect | End | Enum | Else | Exit | Cast | Forall
    | Foreach | Function_ | Mapping | Overload | Throw | Try | Catch | If_ | In | Inc | Var | Ref | Pure | Impure
    | Monadic | Register | Return | Scattered | Sizeof | Constraint | Constant | Struct | Then | Typedef | Union
    | Newtype | With | Val | Outcome | Instantiation | Impl | Private | Repeat | Until | While | Do | Mutual
    | Configuration | TerminationMeasure | Forwards | Backwards | Let_ | Bitfield ->
        mark Highlight.Keyword;
        go ()
    | Pragma _ | Attribute _ | Fixity _ ->
        mark Highlight.Pragma;
        go ()
    | InternalPLet | InternalReturn | InternalAssume ->
        mark Highlight.Internal;
        go ()
    | OpId _ | Star | ColonColon | Bar | Caret | Minus ->
        mark Highlight.Operator;
        go ()
    | Hex _ | Bin _ | Undefined | True | False | Bitzero | Bitone | Num _ | Real _ ->
        mark Highlight.Literal;
        go ()
    | TyVar _ ->
        mark Highlight.TyVar;
        go ()
    | Under | Colon _ | Lcurly | Rcurly | LcurlyBar | RcurlyBar | Lsquare | Rsquare | LsquareBar | RsquareBar | Lparen
    | Rparen | Dot | DotDot | EqGt _ | At | Unit _ | Bidir | Semi | Comma | Eq _ | TwoCaret | MinusGt ->
        go ()
  in
  go ();
  List.iter
    (function Lexer.Comment (_, s, e, _) -> Queue.add (Highlight.Comment, s.pos_cnum, e.pos_cnum) highlights)
    !comments;
  let highlights = Array.init (Queue.length highlights) (fun _ -> Queue.take highlights) in
  Array.stable_sort (fun (_, s1, _) (_, s2, _) -> Int.compare s1 s2) highlights;
  highlights

let hyperlink_targets ast =
  let open Callgraph in
  let targets = ref NodeMap.empty in
  List.iter
    (fun (DEF_aux (_, def_annot) as def) ->
      match Reporting.simp_loc def_annot.loc with
      | Some (p, _) -> NodeSet.iter (fun node -> targets := NodeMap.add node p !targets) (nodes_of_def def)
      | None -> ()
    )
    ast.defs;
  !targets

let hyperlinks_for_file ~filename ast =
  let hyperlinks = Queue.create () in
  List.iter
    (fun def ->
      List.iter
        (fun link ->
          let node = Docinfo.hyperlink_target link in
          let f, s, e = Docinfo.hyperlink_span link in
          if filename = f then Queue.add (node, s, e) hyperlinks
        )
        (Docinfo.hyperlinks_from_def [] def)
    )
    ast.defs;
  let hyperlinks = Array.init (Queue.length hyperlinks) (fun _ -> Queue.take hyperlinks) in
  Array.stable_sort (fun (_, s1, _) (_, s2, _) -> Int.compare s1 s2) hyperlinks;
  hyperlinks

let default_css =
  [
    ".sail-id { color: black; }";
    ".sail-keyword { font-weight: bold; color: maroon; }";
    ".sail-kind { color: purple; }";
    ".sail-comment { color: green; }";
    ".sail-string { color: red; }";
    ".sail-pragma { font-weight: bold; color: blue; }";
    ".sail-internal { font-weight: bold; color: red; }";
    ".sail-operator { color: maroon; }";
    ".sail-literal { color: teal; }";
    ".sail-ty-var { color: blue; }";
    "#sail-html-columns { display: flex; width: 100%; }";
    "#sail-html-lines { padding-left: 10px; padding-right: 10px; width: min-content; text-align: right; white-space: \
     nowrap; }";
    "#sail-html-source { padding-left: 10px; flex: 1; }";
    ":target { background: yellow; }";
  ]
  |> Util.string_of_list "" (fun line -> line ^ "\n")

let output_tags out_chan tags =
  Util.iter_last
    (fun is_last tag ->
      output_string out_chan tag;
      if not is_last then output_char out_chan '\n'
    )
    tags

type file_info = { filename : string; prefix : string; contents : string; highlights : (Highlight.t * int * int) array }

let get_span ~current ~index ~access n =
  match !current with
  | Some (info, s, e) ->
      if e = n then (
        current := None;
        incr index
      );
      Some (info, s, e)
  | None ->
      let rec go () =
        match access !index with
        | info, s, e ->
            if s < n then (
              incr index;
              go ()
            )
            else if s = n then (
              current := Some (info, s, e);
              !current
            )
            else None
        | exception Invalid_argument _ -> None
      in
      go ()

let output_html_char out_chan = function
  | '&' -> output_string out_chan "&amp;"
  | '<' -> output_string out_chan "&lt;"
  | '>' -> output_string out_chan "&gt;"
  | c -> output_char out_chan c

let output_html ?(css = default_css) ~file_info ~hyperlinks out_chan =
  let outputf fmt = Printf.ksprintf (output_string out_chan) fmt in

  let tags_pre_css =
    ["<html>"; "<head>"; "  <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\" />"; "<style>"]
  in
  let tags_post_css =
    ["</style>"; "</head>"; "<body>"; "<pre>"; "<div id=\"sail-html-columns\">"; "<div id=\"sail-html-lines\">"]
  in
  let tags_middle = ["</div>"; "<div id=\"sail-html-source\">"] in
  let tags_end = ["</pre>"; "</div>"; "</div>"; "</body>"; "</html>"] in
  output_tags out_chan tags_pre_css;
  output_string out_chan css;
  output_tags out_chan tags_post_css;

  (* Output the line numbers in the first column div *)
  let line_count = ref 1 in
  String.iter
    (fun c ->
      if c = '\n' then (
        outputf "<span id=\"L%d\">%d</span><br />" !line_count !line_count;
        incr line_count
      )
    )
    file_info.contents;

  output_tags out_chan tags_middle;

  let highlight_index = ref 0 in
  let current_highlight = ref None in
  let get_highlight =
    get_span ~current:current_highlight ~index:highlight_index ~access:(fun i -> file_info.highlights.(i))
  in

  let link_index = ref 0 in
  let current_link = ref None in
  let get_link = get_span ~current:current_link ~index:link_index ~access:(fun i -> hyperlinks.(i)) in

  let starts_on n = function Some (_, s, _) -> n = s | None -> false in

  let ends_on n = function Some (_, _, e) -> n = e | None -> false in

  let highlight_class = function Some (hl, _, _) -> Highlight.to_class hl | None -> assert false in

  let link_target = function Some (t, _, _) -> t | _ -> assert false in

  let highlight_ends_before_link highlight link =
    match (highlight, link) with
    | Some (_, _, highlight_end), Some (_, _, link_end) -> highlight_end < link_end
    | _ -> false
  in

  String.iteri
    (fun n c ->
      let link = get_link n in
      let highlight = get_highlight n in
      (* Insert the starting tags *)
      if starts_on n link then
        if
          (* If there is a current highlight, and it would end before
             the new link ends our HTML tags would be badly nested, so
             fix this by closing the current highlight tag and opening
             a new one. *)
          highlight_ends_before_link highlight link
        then outputf "</span><a href=\"%s\"><span class=\"%s\">" (link_target link) (highlight_class highlight)
        else outputf "<a href=\"%s\">" (link_target link);
      if starts_on n highlight then outputf "<span class=\"%s\">" (highlight_class highlight);
      (* Insert the ending tags *)
      if ends_on n highlight && ends_on n link then (
        output_string out_chan "</span></a>";
        (* Another highlight or link span could start on the same character *)
        match (get_highlight n, get_link n) with
        | Some (hl, hs, _), Some (t, ls, _) when n = hs && n = ls ->
            outputf "<a href=\"%s\"><span class=\"%s\">" t (Highlight.to_class hl)
        | Some (hl, hs, _), _ when n = hs -> outputf "<span class=\"%s\">" (Highlight.to_class hl)
        | _, Some (t, ls, _) when n = ls -> outputf "<a href=\"%s\">" t
        | _, _ -> ()
      )
      else if ends_on n highlight then (
        output_string out_chan "</span>";
        (* Another highlight span could start on the same character *)
        match get_highlight n with
        | Some (hl, hs, _) when n = hs -> outputf "<span class=\"%s\">" (Highlight.to_class hl)
        | _ -> ()
      )
      else if ends_on n link then (
        output_string out_chan "</a>";
        (* Another link span could start on the same character *)
        match get_link n with Some (t, ls, _) when n = ls -> outputf "<a href=\"%s\">" t | _ -> ()
      );
      output_html_char out_chan c
    )
    file_info.contents;

  output_tags out_chan tags_end
