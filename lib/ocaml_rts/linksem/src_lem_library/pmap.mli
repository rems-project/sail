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

(* Modified by Susmit Sarkar 2010-11-30 *)
(* $Id: map.mli 10632 2010-07-24 14:16:58Z garrigue $ *)

(** Association tables over ordered types.

   This module implements applicative association tables, also known as
   finite maps or dictionaries, given a total ordering function
   over the keys.
   All operations over maps are purely applicative (no side-effects).
   The implementation uses balanced binary trees, and therefore searching
   and insertion take time logarithmic in the size of the map.
*)

type ('key,+'a) map
    (** The type of maps from type ['key] to type ['a]. *)

val empty: ('key -> 'key -> int) -> ('key,'a) map
    (** The empty map. *)

val is_empty: ('key,'a) map -> bool
    (** Test whether a map is empty or not. *)

val mem: 'key -> ('key,'a) map -> bool
    (** [mem x m] returns [true] if [m] contains a binding for [x],
       and [false] otherwise. *)

val add: 'key -> 'a -> ('key,'a) map -> ('key,'a) map
    (** [add x y m] returns a map containing the same bindings as
	[m], plus a binding of [x] to [y]. If [x] was already bound
       in [m], its previous binding disappears. *)

val singleton: ('key -> 'key -> int) -> 'key -> 'a -> ('key,'a) map
    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x].
        @since 3.12.0
     *)

val remove: 'key -> ('key,'a) map -> ('key,'a) map
    (** [remove x m] returns a map containing the same bindings as
	[m], except for [x] which is unbound in the returned map. *)

val merge:
    ('key -> 'a option -> 'b option -> 'c option) -> ('key,'a) map -> ('key,'b) map -> ('key,'c) map
    (** [merge f m1 m2] computes a map whose keys is a subset of keys of [m1]
        and of [m2]. The presence of each such binding, and the corresponding
        value, is determined with the function [f].
        @since 3.12.0
     *)

val union: ('key,'a) map -> ('key,'a) map -> ('key,'a) map
    (** [union m1 m2] computes a map whose keys is a subset of keys of [m1]
        and of [m2]. The bindings in m2 take precedence.
        @since 3.12.0
     *)

val compare: ('a -> 'a -> int) -> ('key,'a) map -> ('key,'a) map -> int
    (** Total ordering between maps.  The first argument is a total ordering
        used to compare data associated with equal keys in the two maps. *)

val equal: ('a -> 'a -> bool) -> ('key,'a) map -> ('key,'a) map -> bool
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
	equal, that is, contain equal keys and associate them with
       equal data.  [cmp] is the equality predicate used to compare
       the data associated with the keys. *)

val iter: ('key -> 'a -> unit) -> ('key,'a) map -> unit
    (** [iter f m] applies [f] to all bindings in map [m].
       [f] receives the key as first argument, and the associated value
       as second argument.  The bindings are passed to [f] in increasing
       order with respect to the ordering over the type of the keys. *)

val fold: ('key -> 'a -> 'b -> 'b) -> ('key,'a) map -> 'b -> 'b
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
       where [k1 ... kN] are the keys of all bindings in [m]
       (in increasing order), and [d1 ... dN] are the associated data. *)

val for_all: ('key -> 'a -> bool) -> ('key,'a) map -> bool
    (** [for_all p m] checks if all the bindings of the map
        satisfy the predicate [p].
        @since 3.12.0
     *)

val exist: ('key -> 'a -> bool) -> ('key,'a) map -> bool
    (** [exists p m] checks if at least one binding of the map
        satisfy the predicate [p].
        @since 3.12.0
     *)

val filter: ('key -> 'a -> bool) -> ('key,'a) map -> ('key,'a) map
    (** [filter p m] returns the map with all the bindings in [m]
        that satisfy predicate [p].
        @since 3.12.0
     *)

val partition: ('key -> 'a -> bool) -> ('key,'a) map -> ('key,'a) map * ('key,'a) map
    (** [partition p m] returns a pair of maps [(m1, m2)], where
        [m1] contains all the bindings of [s] that satisfy the
        predicate [p], and [m2] is the map with all the bindings of
        [s] that do not satisfy [p].
        @since 3.12.0
     *)

val cardinal: ('key,'a) map -> int
    (** Return the number of bindings of a map.
        @since 3.12.0
     *)

val bindings_list: ('key,'a) map -> ('key * 'a) list
    (** Return the list of all bindings of the given map.
       The returned list is sorted in increasing order with respect
       to the ordering [Ord.compare], where [Ord] is the argument
       given to {!Map.Make}.
        @since 3.12.0
     *)

val bindings: (('key * 'a) -> ('key * 'a) -> int) -> ('key,'a) map -> ('key * 'a) Pset.set
    (** Return a set of all bindings of the given map. *)

(** [domain m] returns the domain of the map [m], i.e. the
    set of keys of this map. *)
val domain : ('key,'a) map -> 'key Pset.set

(** [range m] returns the range of the map [m], i.e. the
    set of all values stored in this map. *)
val range : ('a -> 'a -> int) -> ('key,'a) map -> 'a Pset.set

val min_binding: ('key,'a) map -> ('key * 'a)
    (** Return the smallest binding of the given map
       (with respect to the [Ord.compare] ordering), or raise
       [Not_found] if the map is empty.
        @since 3.12.0
     *)

val max_binding: ('key,'a) map -> ('key * 'a)
    (** Same as {!Map.S.min_binding}, but returns the largest binding
        of the given map.
        @since 3.12.0
     *)

val choose: ('key,'a) map -> ('key * 'a)
    (** Return one binding of the given map, or raise [Not_found] if
       the map is empty. Which binding is chosen is unspecified,
       but equal bindings will be chosen for equal maps.
        @since 3.12.0
     *)

val split: 'key -> ('key,'a) map -> ('key,'a) map * 'a option * ('key,'a) map
    (** [split x m] returns a triple [(l, data, r)], where
          [l] is the map with all the bindings of [m] whose key
        is strictly less than [x];
          [r] is the map with all the bindings of [m] whose key
        is strictly greater than [x];
          [data] is [None] if [m] contains no binding for [x],
          or [Some v] if [m] binds [v] to [x].
        @since 3.12.0
     *)

val find: 'key -> ('key,'a) map -> 'a
    (** [find x m] returns the current binding of [x] in [m],
       or raises [Not_found] if no such binding exists. *)

val lookup: 'key -> ('key,'a) map -> 'a option
    (** [lookup x m] returns the current binding of [x] in [m]. In contrast to [find],
       it returns [None] instead of raising an exception, if no such binding exists. *)

val map: ('a -> 'b) -> ('key,'a) map -> ('key,'b) map
    (** [map f m] returns a map with same domain as [m], where the
       associated value [a] of all bindings of [m] has been
       replaced by the result of the application of [f] to [a].
       The bindings are passed to [f] in increasing order
       with respect to the ordering over the type of the keys. *)

val mapi: ('key -> 'a -> 'b) -> ('key,'a) map -> ('key,'b) map
    (** Same as {!Map.S.map}, but the function receives as arguments both the
       key and the associated value for each binding of the map. *)

val from_set : ('key -> 'v) -> ('key Pset.set) -> ('key, 'v) map
