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

(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

let opt_warnings = ref true
let opt_colors = ref true
let opt_verbosity = ref 0

let rec last = function
  | [x] -> x
  | _ :: xs -> last xs
  | [] -> raise (Failure "last")

let rec butlast = function
  | [x] -> []
  | x :: xs -> x :: butlast xs
  | [] -> []

module Duplicate(S : Set.S) = struct

type dups = 
  | No_dups of S.t
  | Has_dups of S.elt

let duplicates (x : S.elt list) : dups =
  let rec f x acc = match x with
    | [] -> No_dups(acc)
    | s::rest ->
        if S.mem s acc then
          Has_dups(s)
        else
          f rest (S.add s acc)
  in
    f x S.empty
end

let remove_duplicates l =
  let l' = List.sort Pervasives.compare l in
  let rec aux acc l = match (acc, l) with
      (_, []) -> List.rev acc 
    | ([], x :: xs) -> aux [x] xs
    | (y::ys, x :: xs) -> if (x = y) then aux (y::ys) xs else aux (x::y::ys) xs
  in
  aux [] l'

let remove_dups compare eq l =
  let l' = List.sort compare l in
  let rec aux acc l = match (acc, l) with
      (_, []) -> List.rev acc 
    | ([], x :: xs) -> aux [x] xs
    | (y::ys, x :: xs) -> if (eq x y) then aux (y::ys) xs else aux (x::y::ys) xs
  in
  aux [] l'

let rec power i tothe =
  if tothe <= 0
  then 1
  else i * power i (tothe - 1)

let rec assoc_maybe eq l k =
  match l with
    | [] -> None
    | (k',v)::l -> if (eq k k') then Some v else assoc_maybe eq l k

let rec compare_list f l1 l2 = 
  match (l1,l2) with
    | ([],[]) -> 0
    | (_,[]) -> 1
    | ([],_) -> -1
    | (x::l1,y::l2) ->
        let c = f x y in
          if c = 0 then
            compare_list f l1 l2
          else
            c

let rec split_on_char sep str =
  try
    let sep_pos = String.index str sep in
    String.sub str 0 sep_pos :: split_on_char sep (String.sub str (sep_pos + 1) (String.length str - (sep_pos + 1)))
  with
  | Not_found -> [str]

let map_changed_default d f l =
  let rec g = function
    | [] -> ([],false)
    | x::y ->
        let (r,c) = g y in
          match f x with
            | None -> ((d x)::r,c)
            | Some(x') -> (x'::r,true)
  in
  let (r,c) = g l in
    if c then
      Some(r)
    else
      None

let map_changed f l = map_changed_default (fun x -> x) f l

let rec map_filter (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with [] -> []
    | x :: xs ->
      let xs' = map_filter f xs in
      match (f x) with None -> xs' 
        | Some x' -> x' :: xs'

let list_index p l =
  let rec aux i l =
    match l with [] -> None
        | (x :: xs) -> if p x then Some i else aux (i+1) xs
  in
  aux 0 l

let option_get_exn e = function
  | Some(o) -> o
  | None -> raise e

let option_default d = function
  | None -> d
  | Some(o) -> o

let option_cases op f1 f2 = match op with
  | Some(o) -> f1 o
  | None -> f2 ()

let option_map f = function
  | None -> None
  | Some(o) -> Some(f o)

let option_bind f = function
  | None -> None
  | Some(o) -> f o

let rec option_binop f x y = match x, y with
  | Some x, Some y -> Some (f x y)
  | _ -> None

let rec option_these = function
  | Some x :: xs -> x :: option_these xs
  | None :: xs -> option_these xs
  | [] -> []

let rec option_all = function
  | [] -> Some []
  | None :: _ -> None
  | Some x :: xs ->
     begin match option_all xs with
     | None -> None
     | Some xs -> Some (x :: xs)
     end

let changed2 f g x h y =
  match (g x, h y) with
    | (None,None) -> None
    | (Some(x'),None) -> Some(f x' y)
    | (None,Some(y')) -> Some(f x y')
    | (Some(x'),Some(y')) -> Some(f x' y')

let rec map_all (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  match l with [] -> Some []
    | x :: xs ->
      match (f x) with None -> None
        | Some x' -> option_map (fun xs' -> x' :: xs') (map_all f xs)

let rec option_first f xL =
  match xL with
      [] -> None
    | (x :: xs) -> match f x with None -> option_first f xs | Some s -> Some s

let list_to_front n l =
  if n <= 0 then l else 
  let rec aux acc n l =
    match (n, l) with
        (0, x::xs) -> (x :: (List.rev_append acc xs))
      | (n, x::xs) -> aux (x :: acc) (n-1) xs
      | (_, []) -> (* should not happen *) raise (Failure "list_to_front")
  in aux [] n l

let undo_list_to_front n l =
  if n <= 0 then l else 
  let rec aux acc n y l =
    match (n, l) with
        (0, xs) -> List.rev_append acc (y::xs)
      | (n, x::xs) -> aux (x :: acc) (n-1) y xs
      | (_, []) -> List.rev_append acc [y]
  in match l with [] -> l | y::xs -> aux [] n y xs

let split_after n l =
  if n < 0 then raise (Failure "negative argument to split_after") else
  let rec aux acc n ll = match (n, ll) with
      (0, _)       -> (List.rev acc, ll)
    | (n, x :: xs) -> aux (x :: acc) (n-1) xs
    | _            -> raise (Failure "index too large")
  in aux [] n l

let rec split3 = function
  | (x, y, z) :: xs ->
    let (xs, ys, zs) = split3 xs in
    (x :: xs, y :: ys, z :: zs)
  | [] -> ([], [], [])

let list_mapi (f : int -> 'a -> 'b)  (l : 'a list) : 'b list =
  let rec aux f i l =
     match l with
         [] -> []
       | (x :: xs) -> ((f i x) :: (aux f (i + 1) xs))
  in
    aux f 0 l

let rec list_iter_sep (sf : unit -> unit) (f : 'a -> unit) l : unit =
  match l with
    | []   -> ()
    | [x0] -> f x0
    | (x0 :: x1 :: xs) -> (f x0; sf(); list_iter_sep sf f (x1 :: xs))

let string_to_list s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i-1) (s.[i] :: acc)
  in aux (String.length s - 1) []

module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end )

module IntIntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int * int
  end )


module ExtraSet = functor (S : Set.S) ->
  struct 
    let add_list s l = List.fold_left (fun s x -> S.add x s) s l
    let from_list l = add_list S.empty l
    let list_union l = List.fold_left S.union S.empty l
    let list_inter = function s :: l -> List.fold_left S.inter s l
       | [] -> raise (Failure "ExtraSet.list_inter")
  end;;


let copy_file src dst = 
  let len = 5096 in
  let b = Bytes.make len ' ' in
  let read_len = ref 0 in
  let i = open_in_bin src in
  let o = open_out_bin dst  in
  while (read_len := input i b 0 len; !read_len <> 0) do
    output o b 0 !read_len
  done;
  close_in i;
  close_out o

let move_file src dst =
   if (Sys.file_exists dst) then Sys.remove dst;
   try
     (* try efficient version *)
     Sys.rename src dst
   with Sys_error _ -> 
   begin
     (* OK, do it the the hard way *)
     copy_file src dst;
     Sys.remove src
   end

let same_content_files file1 file2 : bool =
  (Sys.file_exists file1) && (Sys.file_exists file2) && 
  begin
    let s1 = Stream.of_channel (open_in_bin file1) in
    let s2 = Stream.of_channel (open_in_bin file2) in
    let stream_is_empty s = (try Stream.empty s; true with Stream.Failure -> false) in
    try 
      while ((Stream.next s1) = (Stream.next s2)) do () done;
      false
    with Stream.Failure -> stream_is_empty s1 && stream_is_empty s2
  end

(*String formatting *)
let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let string_of_option string_of = function
  | None -> ""
  | Some x -> string_of x

let is_some = function
  | Some _ -> true
  | None -> false

let rec take_drop f = function
  | [] -> ([], [])
  | (x :: xs) when not (f x) -> ([], x :: xs)
  | (x :: xs) ->
     let (ys, zs) = take_drop f xs in
     (x :: ys, zs)

let is_none opt = not (is_some opt)

let rec take n xs = match n, xs with
  | 0, _ -> []
  | n, [] -> []
  | n, (x :: xs) -> x :: take (n - 1) xs

let rec drop n xs = match n, xs with
  | 0, xs -> xs
  | n, [] -> []
  | n, (x :: xs) -> drop (n - 1) xs

let list_init len f =
  let rec list_init' len f acc =
    if acc >= len then []
    else f acc :: list_init' len f (acc + 1)
  in
  list_init' len f 0

let termcode n =
  if !opt_colors then
    "\x1B[" ^ string_of_int n ^ "m"
  else ""

let bold str = termcode 1 ^ str

let darkgray str = termcode 90 ^ str
let red str = termcode 91 ^ str
let green str = termcode 92 ^ str
let yellow str = termcode 93 ^ str
let blue str = termcode 94 ^ str
let magenta str = termcode 95 ^ str
let cyan str = termcode 96 ^ str

let red_bg str = termcode 41 ^ str

let clear str = str ^ termcode 0

let zchar c =
  let zc c = "z" ^ String.make 1 c in
  if Char.code c <= 41 then zc (Char.chr (Char.code c + 16))
  else if Char.code c <= 47 then zc (Char.chr (Char.code c + 23))
  else if Char.code c <= 57 then String.make 1 c
  else if Char.code c <= 64 then zc (Char.chr (Char.code c + 13))
  else if Char.code c <= 90 then String.make 1 c
  else if Char.code c <= 94 then zc (Char.chr (Char.code c - 13))
  else if Char.code c <= 95 then "_"
  else if Char.code c <= 96 then zc (Char.chr (Char.code c - 13))
  else if Char.code c <= 121 then String.make 1 c
  else if Char.code c <= 122 then "zz"
  else if Char.code c <= 126 then zc (Char.chr (Char.code c - 39))
  else raise (Invalid_argument "zchar")

let zencode_string str = "z" ^ List.fold_left (fun s1 s2 -> s1 ^ s2) "" (List.map zchar (string_to_list str))

let zencode_upper_string str = "Z" ^ List.fold_left (fun s1 s2 -> s1 ^ s2) "" (List.map zchar (string_to_list str))

(** Encode string for use as a filename. We can't use zencode directly
   because some operating systems make the mistake of being
   case-insensitive. *)
let file_encode_string str =
  let zstr = zencode_string str in
  let md5 = Digest.to_hex (Digest.string zstr) in
  String.lowercase_ascii zstr ^ String.lowercase_ascii md5

let warn str =
  if !opt_warnings then
    prerr_endline (("Warning" |> yellow |> clear) ^ ": " ^ str)
  else ()

let log_line str line msg =
  "\n[" ^ (str ^ ":" ^ string_of_int line |> blue |> clear) ^ "] " ^ msg

let header str n = "\n" ^ str ^ "\n" ^ String.make (String.length str - 9 * n) '='

let verbose_endline level str =
  if level >= !opt_verbosity then
    prerr_endline str
  else
    ()

let progress prefix msg n total =
  if !opt_verbosity > 0 then
    let len = truncate ((float n /. float total) *. 50.0) in
    let percent = truncate ((float n /. float total) *. 100.0) in
    let msg =
      if String.length msg <= 20 then
        msg ^ ")" ^ String.make (20 - String.length msg) ' '
      else
        String.sub msg 0 17 ^ "...)"
    in
    let str = prefix ^ "[" ^ String.make len '=' ^ String.make (50 - len) ' ' ^ "] "
              ^ string_of_int percent ^ "%"
              ^ " (" ^ msg
    in
    prerr_string str;
    if n = total then
      prerr_char '\n'
    else
      prerr_string ("\x1B[" ^ string_of_int (String.length str) ^ "D");
    flush stderr
  else
    ()
