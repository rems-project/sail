(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

type 'a parse_result =
  | Ok of 'a * Str.split_result list
  | Fail

type 'a parser = Str.split_result list -> 'a parse_result

let (>>=) (m : 'a parser) (f : 'a -> 'b parser) (toks : Str.split_result list) =
  match m toks with
  | Ok (r, toks) -> f r toks
  | Fail -> Fail

let pmap f m toks =
  match m toks with
  | Ok (r, toks) -> Ok (f r, toks)
  | Fail -> Fail

let token f = function
  | tok :: toks ->
     begin match f tok with
     | Some x -> Ok (x, toks)
     | None -> Fail
     end
  | [] -> Fail

let preturn x toks = Ok (x, toks)

let rec plist m toks =
  match m toks with
  | Ok (x, toks) ->
     begin match plist m toks with
     | Ok (xs, toks) -> Ok (x :: xs, toks)
     | Fail -> Fail
     end
  | Fail -> Ok ([], toks)

let pchoose m n toks =
  match m toks with
  | Fail -> n toks
  | Ok (x, toks) -> Ok (x, toks)

let parse p delim_regexp input =
  let delim = Str.regexp delim_regexp in
  let tokens = Str.full_split delim input in
  let non_whitespace = function
    | Str.Delim d when String.trim d = "" -> false
    | _ -> true
  in
  let tokens = List.filter non_whitespace tokens in
  match p tokens with
  | Ok (result, []) -> Some result
  | Ok (result, _) -> None
  | Fail -> None
