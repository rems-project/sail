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

(* Last element of a list *)
val last : 'a list -> 'a

val opt_warnings : bool ref
val opt_colors : bool ref

val butlast : 'a list -> 'a list

(** Mixed useful things *)
module Duplicate(S : Set.S) : sig
  type dups =
    | No_dups of S.t
    | Has_dups of S.elt
  val duplicates : S.elt list -> dups
end

(** [remove_duplicates l] removes duplicate elements from
    the list l. As a side-effect, the list might be reordered. *)
val remove_duplicates : 'a list -> 'a list

(** [remove_dups compare eq l] as remove_duplicates but with parameterised comparison and equality *)
val remove_dups : ('a -> 'a -> int) -> ('a -> 'a -> bool) -> 'a list -> 'a list

val assoc_maybe : ('a -> 'a -> bool) -> ('a * 'b) list -> 'a -> 'b option

val power : int -> int -> int

(** {2 Option Functions} *)

(** [option_map f None] returns [None], whereas
    [option_map f (Some x)] returns [Some (f x)]. *)
val option_map : ('a -> 'b) -> 'a option -> 'b option

(** [option_cases None f_s f_n] returns [f_n], whereas
    [option_cases (Some x) f_s f_n] returns [f_s x]. *)
val option_cases : 'a option -> ('a -> 'b) -> (unit -> 'b) -> 'b

(** [option_bind f None] returns [None], whereas
    [option_bind f (Some x)] returns [f x]. *)
val option_bind : ('a -> 'b option) -> 'a option -> 'b option

(** [option_default d None] returns the default value [d], 
    whereas [option_default d (Some x)] returns [x]. *)
val option_default : 'a -> 'a option -> 'a

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

(** [changed2 f g x h y] applies [g] to [x] and [h] to [y].
    If both function applications return [None], then [None] is
    returned. Otherwise [f] is applied to the results. For this
    application of [f], [x] is used in case [g x] returns [None] and
    similarly [y] in case [h y] returns [None]. *)
val changed2 : ('a -> 'b -> 'c) -> ('a -> 'a option) -> 'a -> ('b -> 'b option) -> 'b -> 'c option

(** {2 List Functions} *)

(** [list_index p l] returns the first index [i] such that
    the predicate [p (l!i)] holds. If no such [i] exists,
    [None] is returned. *)
val list_index: ('a -> bool) -> 'a list -> int option

(** [option_first f l] searches for the first element [x] of [l] such
    that the [f x] is not [None]. If such an element exists, [f x] is
    returned, otherwise [None]. *)
val option_first: ('a -> 'b option) -> 'a list -> 'b option

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

(** [list_mapi f l] maps [f] over [l]. In contrast to the standard
    [map] function, [f] gets the current index of the list as an extra
    argument. Counting starts at [0]. *)
val list_mapi : (int -> 'a -> 'b) -> 'a list -> 'b list

(** [list_iter sf f [a1; ...; an]] applies function [f] in turn to [a1; ...; an] and
    calls [sf ()] in between. It is equivalent to [begin f a1; sf(); f a2; sf(); ...; f an; () end]. *)
val list_iter_sep : (unit -> unit) -> ('a -> unit) -> 'a list -> unit 

(** [map_filter f l] maps [f] over [l] and removes all entries [x] of [l]
    with [f x = None]. *)
val map_filter : ('a -> 'b option) -> 'a list -> 'b list

(** [map_all f l] maps [f] over [l]. If at least one entry is [None], [None] is returned. Otherwise,
    the [Some] function is removed from the list. *)
val map_all : ('a -> 'b option) -> 'a list -> 'b list option

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


(** {2 Files} *)

(** [copy_file src dst] copies file [src] to file [dst]. Only files are supported,
    no directories. *)
val copy_file : string -> string -> unit

(** [move_file src dst] moves file [src] to file [dst]. In contrast to [Sys.rename] no error is
    produced, if [dst] already exists. Moreover, in case [Sys.rename] fails for some reason (e.g. because
    it does not work over filesystem boundaries), [copy_file] and [Sys.remove] are used as
    fallback. *)
val move_file : string -> string -> unit

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

(** Some useful extra functions for sets *)
module ExtraSet : functor (S : Set.S) ->
   sig
     (** Add a list of values to an existing set. *)
     val add_list : S.t -> S.elt list -> S.t

     (** Construct a set from a list. *)
     val from_list : S.elt list -> S.t

     (** Builds the union of a list of sets  *)
     val list_union : S.t list -> S.t

     (** Builds the intersection of a list of sets.
         If the list is empty, a match exception is thrown. *)
     val list_inter : S.t list -> S.t
   end

val list_init : int -> (int -> 'a) -> 'a list

(*Formatting functions*)
val string_of_list : string -> ('a -> string) -> 'a list -> string

val string_of_option : ('a -> string) -> 'a option -> string

val split_on_char : char -> string -> string list

val is_some : 'a option -> bool
val is_none : 'a option -> bool

val take : int -> 'a list -> 'a list
val drop : int -> 'a list -> 'a list

val take_drop : ('a -> bool) -> 'a list -> ('a list * 'a list)

(* Terminal color codes *)
val termcode : int -> string
val bold : string -> string
val darkgray : string -> string
val green : string -> string
val red : string -> string
val red_bg : string -> string
val yellow : string -> string
val cyan : string -> string
val blue : string -> string
val magenta : string -> string
val clear : string -> string

val warn : string -> unit

val zencode_string : string -> string
val zencode_upper_string : string -> string

val file_encode_string : string -> string

val log_line : string -> int -> string -> string
val header : string -> int -> string
