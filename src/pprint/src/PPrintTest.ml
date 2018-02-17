(**************************************************************************)
(*                                                                        *)
(*  PPrint                                                                *)
(*                                                                        *)
(*  François Pottier, Inria Paris                                         *)
(*  Nicolas Pouillard                                                     *)
(*                                                                        *)
(*  Copyright 2007-2017 Inria. All rights reserved. This file is          *)
(*  distributed under the terms of the GNU Library General Public         *)
(*  License, with an exception, as described in the file LICENSE.         *)
(*                                                                        *)
(**************************************************************************)

open PPrint

(* This is a test file. It is not, strictly speaking, part of the library. *)

let paragraph (s : string) =
  flow (break 1) (words s)

let document =
  prefix 2 1
    (string "TITLE:")
    (string "PPrint")
  ^^
  hardline
  ^^
  prefix 2 1
    (string "AUTHORS:")
    (utf8string "François Pottier and Nicolas Pouillard")
  ^^
  hardline
  ^^
  prefix 2 1
    (string "ABSTRACT:")
    (
      paragraph "This is an adaptation of Daan Leijen's \"PPrint\" library,
        which itself is based on the ideas developed by Philip Wadler in
        \"A Prettier Printer\". For more information about Wadler's and Leijen's work,
        please consult the following references:"
      ^^
      nest 2 (
	twice (break 1)
	^^
	separate_map (break 1) (fun s -> nest 2 (url s)) [
	  "http://www.cs.uu.nl/~daan/pprint.html";
	  "http://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf";
	]
      )
      ^^
      twice (break 1)
      ^^
      paragraph "To install PPrint, type \"make -C src install\". ocamlfind is required."
      ^^
      twice (break 1)
      ^^
      paragraph "The documentation for PPrint is built by \"make doc\" and is found in the file doc/index.html."
    )
  ^^
  hardline

let () =
  ToChannel.pretty 0.5 80 stdout document;
  flush stdout
