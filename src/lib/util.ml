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

let opt_colors = ref true
let opt_verbosity = ref 0

let rec last = function [x] -> x | _ :: xs -> last xs | [] -> raise (Failure "last")

let rec last_opt = function [x] -> Some x | _ :: xs -> last_opt xs | [] -> None

let rec butlast = function [_] -> [] | x :: xs -> x :: butlast xs | [] -> []

module Duplicate (S : Set.S) = struct
  type dups = No_dups of S.t | Has_dups of S.elt

  let duplicates (x : S.elt list) : dups =
    let rec f x acc =
      match x with [] -> No_dups acc | s :: rest -> if S.mem s acc then Has_dups s else f rest (S.add s acc)
    in
    f x S.empty
end

let remove_duplicates l =
  let l' = List.sort Stdlib.compare l in
  let rec aux acc l =
    match (acc, l) with
    | _, [] -> List.rev acc
    | [], x :: xs -> aux [x] xs
    | y :: ys, x :: xs -> if x = y then aux (y :: ys) xs else aux (x :: y :: ys) xs
  in
  aux [] l'

let remove_dups compare eq l =
  let l' = List.sort compare l in
  let rec aux acc l =
    match (acc, l) with
    | _, [] -> List.rev acc
    | [], x :: xs -> aux [x] xs
    | y :: ys, x :: xs -> if eq x y then aux (y :: ys) xs else aux (x :: y :: ys) xs
  in
  aux [] l'

let lex_ord_list comparison xs ys =
  let rec lex_lists xs ys =
    match (xs, ys) with
    | x :: xs, y :: ys ->
        let c = comparison x y in
        if c = 0 then lex_lists xs ys else c
    | [], [] -> 0
    | _, _ -> assert false
  in
  let c = List.compare_lengths xs ys in
  if c = 0 then lex_lists xs ys else c

let rec power i tothe = if tothe <= 0 then 1 else i * power i (tothe - 1)

let rec assoc_equal_opt eq k l =
  match l with [] -> None | (k', v) :: l -> if eq k k' then Some v else assoc_equal_opt eq k l

let rec assoc_compare_opt cmp k l =
  match l with [] -> None | (k', v) :: l -> if cmp k k' = 0 then Some v else assoc_compare_opt cmp k l

let rec compare_list f l1 l2 =
  match (l1, l2) with
  | [], [] -> 0
  | _, [] -> 1
  | [], _ -> -1
  | x :: l1, y :: l2 ->
      let c = f x y in
      if c = 0 then compare_list f l1 l2 else c

let rec map_last f = function [] -> [] | [x] -> [f true x] | x :: xs -> f false x :: map_last f xs

let rec iter_last f = function
  | [] -> ()
  | [x] -> f true x
  | x :: xs ->
      f false x;
      iter_last f xs

let rec split_on_char sep str =
  try
    let sep_pos = String.index str sep in
    String.sub str 0 sep_pos :: split_on_char sep (String.sub str (sep_pos + 1) (String.length str - (sep_pos + 1)))
  with Not_found -> [str]

let map_changed_default d f l =
  let rec g = function
    | [] -> ([], false)
    | x :: y -> (
        let r, c = g y in
        match f x with None -> (d x :: r, c) | Some x' -> (x' :: r, true)
      )
  in
  let r, c = g l in
  if c then Some r else None

let map_changed f l = map_changed_default (fun x -> x) f l

let rec map_split f = function
  | [] -> ([], [])
  | x :: xs -> (
      match f x with
      | Ok x' ->
          let xs', ys' = map_split f xs in
          (x' :: xs', ys')
      | Error y' ->
          let xs', ys' = map_split f xs in
          (xs', y' :: ys')
    )

let list_empty = function [] -> true | _ -> false

let list_index p l =
  let rec aux i l = match l with [] -> None | x :: xs -> if p x then Some i else aux (i + 1) xs in
  aux 0 l

let option_get_exn e = function Some o -> o | None -> raise e

let option_cases op f1 f2 = match op with Some o -> f1 o | None -> f2 ()

let option_binop f x y = match (x, y) with Some x, Some y -> Some (f x y) | _ -> None

let rec option_these = function Some x :: xs -> x :: option_these xs | None :: xs -> option_these xs | [] -> []

let rec option_all = function
  | [] -> Some []
  | None :: _ -> None
  | Some x :: xs -> begin match option_all xs with None -> None | Some xs -> Some (x :: xs) end

let rec map_all (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  match l with
  | [] -> Some []
  | x :: xs -> (
      match f x with None -> None | Some x' -> Option.map (fun xs' -> x' :: xs') (map_all f xs)
    )

let rec option_first f xL =
  match xL with
  | [] -> None
  | x :: xs -> (
      match f x with None -> option_first f xs | Some s -> Some s
    )

let list_to_front n l =
  if n <= 0 then l
  else (
    let rec aux acc n l =
      match (n, l) with
      | 0, x :: xs -> x :: List.rev_append acc xs
      | n, x :: xs -> aux (x :: acc) (n - 1) xs
      | _, [] -> (* should not happen *) raise (Failure "list_to_front")
    in
    aux [] n l
  )

let undo_list_to_front n l =
  if n <= 0 then l
  else (
    let rec aux acc n y l =
      match (n, l) with
      | 0, xs -> List.rev_append acc (y :: xs)
      | n, x :: xs -> aux (x :: acc) (n - 1) y xs
      | _, [] -> List.rev_append acc [y]
    in
    match l with [] -> l | y :: xs -> aux [] n y xs
  )

let split_after n l =
  if n < 0 then raise (Failure "negative argument to split_after")
  else (
    let rec aux acc n ll =
      match (n, ll) with
      | 0, _ -> (List.rev acc, ll)
      | n, x :: xs -> aux (x :: acc) (n - 1) xs
      | _ -> raise (Failure "index too large")
    in
    aux [] n l
  )

let rec split3 = function
  | (x, y, z) :: xs ->
      let xs, ys, zs = split3 xs in
      (x :: xs, y :: ys, z :: zs)
  | [] -> ([], [], [])

let rec list_iter_sep (sf : unit -> unit) (f : 'a -> unit) l : unit =
  match l with
  | [] -> ()
  | [x0] -> f x0
  | x0 :: x1 :: xs ->
      f x0;
      sf ();
      list_iter_sep sf f (x1 :: xs)

let string_to_list s =
  let rec aux i acc = if i < 0 then acc else aux (i - 1) (s.[i] :: acc) in
  aux (String.length s - 1) []

module IntSet = Set.Make (struct
  let compare = Stdlib.compare
  type t = int
end)

module IntIntSet = Set.Make (struct
  let compare = Stdlib.compare
  type t = int * int
end)

let copy_file src dst =
  let len = 5096 in
  let b = Bytes.make len ' ' in
  let read_len = ref 0 in
  let i = open_in_bin src in
  let o = open_out_bin dst in
  while
    read_len := input i b 0 len;
    !read_len <> 0
  do
    output o b 0 !read_len
  done;
  close_in i;
  close_out o

let move_file src dst =
  if Sys.file_exists dst then Sys.remove dst;
  try (* try efficient version *)
      Sys.rename src dst
  with Sys_error _ ->
    (* OK, do it the the hard way *)
    copy_file src dst;
    Sys.remove src

let input_byte_opt chan = try Some (input_byte chan) with End_of_file -> None

let same_content_files file1 file2 : bool =
  Sys.file_exists file1 && Sys.file_exists file2
  && begin
       let s1 = open_in_bin file1 in
       let s2 = open_in_bin file2 in
       let rec comp s1 s2 =
         match (input_byte_opt s1, input_byte_opt s2) with
         | None, None -> true
         | Some b1, Some b2 -> if b1 = b2 then comp s1 s2 else false
         | _, _ -> false
       in
       let result = comp s1 s2 in
       close_in s1;
       close_in s2;
       result
     end

(*String formatting *)
let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x :: ls -> string_of x ^ sep ^ string_of_list sep string_of ls

let string_of_option string_of = function None -> "" | Some x -> string_of x

let rec take_drop f = function
  | [] -> ([], [])
  | x :: xs when not (f x) -> ([], x :: xs)
  | x :: xs ->
      let ys, zs = take_drop f xs in
      (x :: ys, zs)

let rec find_rest_opt f = function [] -> None | x :: xs when f x -> Some (x, xs) | _ :: xs -> find_rest_opt f xs

let find_next f xs =
  let rec find_next' f acc = function
    | x :: xs when f x -> (List.rev acc, Some (x, xs))
    | x :: xs -> find_next' f (x :: acc) xs
    | [] -> (List.rev acc, None)
  in
  find_next' f [] xs

let find_index_opt f xs =
  let rec find_index_opt' f i = function
    | x :: _ when f x -> Some (i, x)
    | _ :: xs -> find_index_opt' f (i + 1) xs
    | [] -> None
  in
  find_index_opt' f 0 xs

let rec find_map f = function
  | x :: xs -> begin match f x with Some y -> Some y | None -> find_map f xs end
  | [] -> None

let fold_left_concat_map f acc xs =
  let ys, acc =
    List.fold_left
      (fun (ys, acc) x ->
        let acc, zs = f acc x in
        (List.rev zs @ ys, acc)
      )
      ([], acc) xs
  in
  (acc, List.rev ys)

let rec fold_left_last f acc = function
  | [] -> acc
  | [x] -> f true acc x
  | x :: xs -> fold_left_last f (f false acc x) xs

let fold_left_index f init xs =
  let rec go n acc = function [] -> acc | x :: xs -> go (n + 1) (f n acc x) xs in
  go 0 init xs

let fold_left_index_last f init xs =
  let rec go n acc = function [] -> acc | [x] -> f n true acc x | x :: xs -> go (n + 1) (f n false acc x) xs in
  go 0 init xs

let map_if pred f xs =
  let rec go acc = function
    | x :: xs -> begin match pred x with true -> go (f x :: acc) xs | false -> go (x :: acc) xs end
    | [] -> List.rev acc
  in
  go [] xs

let rec map_exists pred f = function x :: xs -> if pred (f x) then true else map_exists pred f xs | [] -> false

let rec take n xs = match (n, xs) with 0, _ -> [] | _, [] -> [] | n, x :: xs -> x :: take (n - 1) xs

let rec drop n xs = match (n, xs) with 0, xs -> xs | _, [] -> [] | n, _ :: xs -> drop (n - 1) xs

let list_init len f =
  let rec list_init' len f acc = if acc >= len then [] else f acc :: list_init' len f (acc + 1) in
  list_init' len f 0

let termcode n = if !opt_colors then "\x1B[" ^ string_of_int n ^ "m" else ""

let bold str = termcode 1 ^ str
let dim str = termcode 2 ^ str

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

let file_encode_string str =
  let zstr = zencode_string str in
  let md5 = Digest.to_hex (Digest.string zstr) in
  String.lowercase_ascii zstr ^ String.lowercase_ascii md5

let log_line str line msg = "\n[" ^ (str ^ ":" ^ string_of_int line |> blue |> clear) ^ "] " ^ msg

let header str n = "\n" ^ str ^ "\n" ^ String.make (String.length str - (9 * n)) '='

let progress prefix msg n total =
  if !opt_verbosity > 0 then (
    let len = truncate (float n /. float total *. 50.0) in
    let percent = truncate (float n /. float total *. 100.0) in
    let msg =
      if String.length msg <= 20 then msg ^ ")" ^ String.make (20 - String.length msg) ' '
      else String.sub msg 0 17 ^ "...)"
    in
    let str =
      prefix ^ "[" ^ String.make len '=' ^ String.make (50 - len) ' ' ^ "] " ^ string_of_int percent ^ "%" ^ " (" ^ msg
    in
    prerr_string str;
    if n = total then prerr_char '\n' else prerr_string ("\x1B[" ^ string_of_int (String.length str) ^ "D");
    flush stderr
  )
  else ()

let open_output_with_check opt_dir file_name =
  let temp_file_name, o = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  (o', (o, temp_file_name, opt_dir, file_name))

let open_output_with_check_unformatted opt_dir file_name =
  let temp_file_name, o = Filename.open_temp_file "ll_temp" "" in
  (o, temp_file_name, opt_dir, file_name)

let always_replace_files = ref true

let close_output_with_check (o, temp_file_name, opt_dir, file_name) =
  let _ = close_out o in
  let file_name =
    match opt_dir with
    | None -> file_name
    | Some dir ->
        if Sys.file_exists dir then () else Unix.mkdir dir 0o775;
        Filename.concat dir file_name
  in
  let do_replace = !always_replace_files || not (same_content_files temp_file_name file_name) in
  let _ = if not do_replace then Sys.remove temp_file_name else move_file temp_file_name file_name in
  ()
