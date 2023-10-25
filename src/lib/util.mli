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

(** Various non Sail specific utility functions *)

val opt_colors : bool ref
val opt_verbosity : int ref

(* Last element of a list *)
val last : 'a list -> 'a

val last_opt : 'a list -> 'a option

val butlast : 'a list -> 'a list

(** Mixed useful things *)
module Duplicate (S : Set.S) : sig
  type dups = No_dups of S.t | Has_dups of S.elt
  val duplicates : S.elt list -> dups
end

(** [remove_duplicates l] removes duplicate elements from
    the list l. As a side-effect, the list might be reordered. *)
val remove_duplicates : 'a list -> 'a list

(** [remove_dups compare eq l] as remove_duplicates but with parameterised comparison and equality *)
val remove_dups : ('a -> 'a -> int) -> ('a -> 'a -> bool) -> 'a list -> 'a list

(** Lift a comparison order to the lexical order on lists *)
val lex_ord_list : ('a -> 'a -> int) -> 'a list -> 'a list -> int

(** [assoc_equal_opt] and [assoc_compare_opt] are like List.assoc_opt
   but take equality/comparison functions as arguments, rather than
   relying on OCaml's built in equality *)
val assoc_equal_opt : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b option

val assoc_compare_opt : ('a -> 'a -> int) -> 'a -> ('a * 'b) list -> 'b option

val power : int -> int -> int

(** Map but pass true to the function for the last element *)
val map_last : (bool -> 'a -> 'b) -> 'a list -> 'b list

val iter_last : (bool -> 'a -> unit) -> 'a list -> unit

(** {2 Option Functions} *)

(** [option_cases None f_s f_n] returns [f_n], whereas
    [option_cases (Some x) f_s f_n] returns [f_s x]. *)
val option_cases : 'a option -> ('a -> 'b) -> (unit -> 'b) -> 'b

(** [option_binop f (Some x) (Some y)] returns [Some (f x y)],
    and in all other cases, [option_binop] returns [None]. *)
val option_binop : ('a -> 'a -> 'b) -> 'a option -> 'a option -> 'b option

(** [option_get_exn exn None] throws the exception [exn],
    whereas [option_get_exn exn (Some x)] returns [x]. *)
val option_get_exn : exn -> 'a option -> 'a

(** [option_these xs] extracts the elements of the list [xs]
    wrapped in [Some]. *)
val option_these : 'a option list -> 'a list

(** [option_all xs] extracts the elements of the list [xs] if all of
   them are wrapped in Some. If any are None then the result is None is
   None. [option_all []] is [Some []] *)
val option_all : 'a option list -> 'a list option

(** {2 List Functions} *)

val list_empty : 'a list -> bool

(** [list_index p l] returns the first index [i] such that
    the predicate [p (l!i)] holds. If no such [i] exists,
    [None] is returned. *)
val list_index : ('a -> bool) -> 'a list -> int option

(** [option_first f l] searches for the first element [x] of [l] such
    that the [f x] is not [None]. If such an element exists, [f x] is
    returned, otherwise [None]. *)
val option_first : ('a -> 'b option) -> 'a list -> 'b option

(** [map_changed f l] maps [f] over [l].
    If for all elements of [l] the
    function [f] returns [None], then [map_changed f l] returns [None].
    Otherwise, it uses [x] for all elements, where [f x] returns [None],
    and returns the resulting list. *)
val map_changed : ('a -> 'a option) -> 'a list -> 'a list option

(** [map_changed_default d f l] maps [f] over [l].
    If for all elements of [l] the
    function [f] returns [None], then [map_changed f l] returns [None].
    Otherwise, it uses [d x] for all elements [x], where [f x] returns [None],
    and returns the resulting list. *)
val map_changed_default : ('a -> 'b) -> ('a -> 'b option) -> 'a list -> 'b list option

(** [list_iter sf f [a1; ...; an]] applies function [f] in turn to [a1; ...; an] and
    calls [sf ()] in between. It is equivalent to [begin f a1; sf(); f a2; sf(); ...; f an; () end]. *)
val list_iter_sep : (unit -> unit) -> ('a -> unit) -> 'a list -> unit

val map_split : ('a -> ('b, 'c) result) -> 'a list -> 'b list * 'c list

(** [map_all f l] maps [f] over [l]. If at least one entry is [None], [None] is returned. Otherwise,
    the [Some] function is removed from the list. *)
val map_all : ('a -> 'b option) -> 'a list -> 'b list option

val map_if : ('a -> bool) -> ('a -> 'a) -> 'a list -> 'a list

val map_exists : ('b -> bool) -> ('a -> 'b) -> 'a list -> bool

(** [list_to_front i l] resorts the list [l] by bringing the element at index [i]
    to the front. 
    @throws Failure if [i] is not smaller than the length of [l]*)
val list_to_front : int -> 'a list -> 'a list

(** [undo_list_to_front i l] resorts the list [l] by moving the head element to index index [i]
    It's the inverse of [list_to_front i l]. *)
val undo_list_to_front : int -> 'a list -> 'a list

(** [split_after n l] splits the first [n] elemenst from list [l], i.e. it returns two lists
    [l1] and [l2], with [length l1 = n] and [l1 @ l2 = l]. Fails if n is too small or large. *)
val split_after : int -> 'a list -> 'a list * 'a list

(** [split3 l] splits a list of triples into a triple of lists *)
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int

val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list

val take_drop : ('a -> bool) -> 'a list -> 'a list * 'a list

val find_rest_opt : ('a -> bool) -> 'a list -> ('a * 'a list) option

val find_next : ('a -> bool) -> 'a list -> 'a list * ('a * 'a list) option

(** find an item in a list and return that item as well as its index *)
val find_index_opt : ('a -> bool) -> 'a list -> (int * 'a) option

val find_map : ('a -> 'b option) -> 'a list -> 'b option

val fold_left_concat_map : ('a -> 'b -> 'a * 'c list) -> 'a -> 'b list -> 'a * 'c list

val fold_left_last : (bool -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_left_index : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_left_index_last : (int -> bool -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val list_init : int -> (int -> 'a) -> 'a list

(** {2 Files} *)

(** [copy_file src dst] copies file [src] to file [dst]. Only files are supported,
    no directories. *)
val copy_file : string -> string -> unit

(** [move_file src dst] moves file [src] to file [dst]. In contrast to [Sys.rename] no error is
    produced, if [dst] already exists. Moreover, in case [Sys.rename] fails for some reason (e.g. because
    it does not work over filesystem boundaries), [copy_file] and [Sys.remove] are used as
    fallback. *)
val move_file : string -> string -> unit

(** [input_byte_opt chan] tries to read a byte [b] from input channel [chan], and
    returns [Some b] in case of success, or [None] if the end of the file was reached. *)
val input_byte_opt : in_channel -> int option

(** [same_content_files file1 file2] checks, whether the files [file1] and [file2] have the same content.
If at least one of the files does not exist, [false] is returned. [same_content_files] throws an exception,
if one of the files exists, but cannot be read. *)
val same_content_files : string -> string -> bool

(** {2 Strings} *)

(** [string_to_list l] translates the string [l] to the list of its characters. *)
val string_to_list : string -> char list

(** {2 Useful Sets} *)

(** Sets of Integers *)
module IntSet : Set.S with type elt = int

module IntIntSet : Set.S with type elt = int * int

(** {2 Formatting functions} *)

val string_of_list : string -> ('a -> string) -> 'a list -> string

val string_of_option : ('a -> string) -> 'a option -> string

val split_on_char : char -> string -> string list

(** {2 Terminal color codes} *)

val termcode : int -> string
val bold : string -> string
val dim : string -> string
val darkgray : string -> string
val green : string -> string
val red : string -> string
val red_bg : string -> string
val yellow : string -> string
val cyan : string -> string
val blue : string -> string
val magenta : string -> string
val clear : string -> string

(** {2 Encoding schemes for strings} *)

(** z-encoding will take any string with ASCII characters in the range
   32-126 inclusive, and map it to a string that just contains ASCII
   upper and lower case letters and numbers, prefixed with the letter
   z. This mapping is one-to-one. *)

val zencode_string : string -> string
val zencode_upper_string : string -> string

(** Encode string for use as a filename. We can't use zencode directly
   because some operating systems make the mistake of being
   case-insensitive. *)
val file_encode_string : string -> string

(** {2 Misc output functions} *)

val log_line : string -> int -> string -> string

val header : string -> int -> string

val progress : string -> string -> int -> int -> unit

(** [always_replace_files] determines whether Sail only updates modified files.
    If it is set to [true], all output files are written, regardless of whether the
    files existed before. If it is set to [false] and an output file already exists,
    the output file is only updated, if its content really changes. *)
val always_replace_files : bool ref

val open_output_with_check :
  string option -> string -> Format.formatter * (out_channel * string * string option * string)

val open_output_with_check_unformatted : string option -> string -> out_channel * string * string option * string

val close_output_with_check : out_channel * string * string option * string -> unit
