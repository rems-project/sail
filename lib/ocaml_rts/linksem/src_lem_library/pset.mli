(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Modified by Scott Owens 2010-10-28 *)

(* $Id: set.mli 6974 2005-07-21 14:52:45Z doligez $ *)

(** Sets over ordered types.

  This module implements the set data structure, given a total ordering
  function over the set elements. All operations over sets
  are purely applicative (no side-effects).
  The implementation uses balanced binary trees, and is therefore
  reasonably efficient: insertion and membership take time
  logarithmic in the size of the set, for instance.
  *)

type 'a set
(** The type of sets. *)

val empty: ('a -> 'a -> int) -> 'a set
(** The empty set. *)

val is_empty: 'a set -> bool
(** Test whether a set is empty or not. *)

val from_list: ('a -> 'a -> int) -> 'a list -> 'a set

val mem: 'a -> 'a set -> bool
(** [mem x s] tests whether [x] belongs to the set [s]. *)

val add: 'a -> 'a set -> 'a set
(** [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

val singleton: ('a -> 'a -> int) -> 'a -> 'a set
(** [singleton x] returns the one-element set containing only [x]. *)

val remove: 'a -> 'a set -> 'a set
(** [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged. *)

val union: 'a set -> 'a set -> 'a set
(** Set union. *)

val inter: 'a set -> 'a set -> 'a set
(** Set intersection. *)

(** Set difference. *)
val diff: 'a set -> 'a set -> 'a set

val compare: 'a set -> 'a set -> int
(** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

val equal: 'a set -> 'a set -> bool
(** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

val subset: 'a set -> 'a set -> bool
(** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. This includes the case where [s1] and [s2] are equal. *)

val subset_proper : 'a set -> 'a set -> bool
(** [subset_proper s1 s2] tests whether the set [s1] is a proper subset of
  the set [s2]. *)

val iter: ('a -> unit) -> 'a set -> unit
(** [iter f s] applies [f] in turn to all elements of [s].
  The elements of [s] are presented to [f] in increasing order
  with respect to the ordering over the type of the elements. *)

val fold: ('a -> 'b -> 'b) -> 'a set -> 'b -> 'b
(** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s], in increasing order. *)

val map: ('b -> 'b -> int) -> ('a -> 'b) -> 'a set -> 'b set

val map_union: ('b -> 'b -> int) -> ('a -> 'b set) -> 'a set -> 'b set
(** [map_union cmp f s] does the same as [bigunion cmp (map cmp' f s)].
    Because the set of sets is internally not constructed though the comparison function [cmp'] is
    not needed. *)

val for_all: ('a -> bool) -> 'a set -> bool
(** [for_all p s] checks if all elements of the set
  satisfy the predicate [p]. *)

val exists: ('a -> bool) -> 'a set -> bool
(** [exists p s] checks if at least one element of
  the set satisfies the predicate [p]. *)

val filter: ('a -> bool) -> 'a set -> 'a set
(** [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p]. *)

val partition: ('a -> bool) -> 'a set -> 'a set * 'a set
(** [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p]. *)

val cardinal: 'a set -> int
(** Return the number of elements of a set. *)

val elements: 'a set -> 'a list
(** Return the list of all elements of the given set.
  The returned list is sorted in increasing order with respect
  to the ordering [Ord.compare], where [Ord] is the argument
  given to {!Set.Make}. *)

val min_elt: 'a set -> 'a
(** Return the smallest element of the given set
  (with respect to the [Ord.compare] ordering), or raise
  [Not_found] if the set is empty. *)

val max_elt: 'a set -> 'a
(** Same as {!Set.S.min_elt}, but returns the largest element of the
  given set. *)

val min_elt_opt: 'a set -> 'a option
(** an optional version of [min_elt] *)

val max_elt_opt: 'a set -> 'a option
(** an optional version of [max_elt] *)

val choose: 'a set -> 'a
(** Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified,
  but equal elements will be chosen for equal sets. *)

val set_case: 'a set -> 'b -> ('a -> 'b) -> 'b -> 'b
(** case-split function for sets *)

val split: 'a -> 'a set -> 'a set * bool * 'a set
    (** [split x s] returns a triple [(l, present, r)], where
      [l] is the set of elements of [s] that are
      strictly less than [x];
      [r] is the set of elements of [s] that are
      strictly greater than [x];
      [present] is [false] if [s] contains no element equal to [x],
      or [true] if [s] contains an element equal to [x]. *)

val comprehension1 : ('b -> 'b -> int) -> ('a -> 'b) -> ('a -> bool) -> 'a set -> 'b set
val comprehension2 : ('c -> 'c -> int) -> ('a -> 'b -> 'c) -> ('a -> 'b -> bool) -> 'a set -> 'b set -> 'c set
val comprehension3 : ('d -> 'd -> int) -> ('a -> 'b -> 'c -> 'd) -> ('a -> 'b -> 'c -> bool) -> 'a set -> 'b set -> 'c set -> 'd set
val comprehension4 : ('e -> 'e -> int) -> ('a -> 'b -> 'c -> 'd -> 'e) -> ('a -> 'b -> 'c -> 'd -> bool) -> 'a set -> 'b set -> 'c set -> 'd set -> 'e set
val comprehension5 : ('f -> 'f -> int) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f) -> ('a -> 'b -> 'c -> 'd -> 'e -> bool) -> 'a set -> 'b set -> 'c set -> 'd set -> 'e set -> 'f set
val comprehension6 : ('g -> 'g -> int) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> bool) -> 'a set -> 'b set -> 'c set -> 'd set -> 'e set -> 'f set -> 'g set
val comprehension7 : ('h -> 'h -> int) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> bool) -> 'a set -> 'b set -> 'c set -> 'd set -> 'e set -> 'f set -> 'g set -> 'h set

val bigunion : ('a -> 'a -> int) -> 'a set set -> 'a set

val lfp : 'a set -> ('a set -> 'a set) -> 'a set
val tc : ('a * 'a -> 'a * 'a -> int) -> ('a * 'a) set -> ('a * 'a) set


val sigma : ('a * 'b -> 'a * 'b -> int) -> 'a set -> ('a -> 'b set) -> ('a * 'b) set
val cross : ('a * 'b -> 'a * 'b -> int) -> 'a set -> 'b set -> ('a * 'b) set

val get_elem_compare : 'a set -> ('a -> 'a -> int)

val compare_by: ('a->'a->int) -> 'a set -> 'a set -> int
(** set comparison parameterised by element comparison (ignoring the comparison functions of the argument sets*)

