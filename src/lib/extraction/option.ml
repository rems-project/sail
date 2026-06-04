open Datatypes
open Base

type __ = Obj.t

(** val from_option : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let from_option f y = function
| Some x -> f x
| None -> y

(** val option_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 option, 'a1 option) coq_RelDecision **)

let option_eq_dec dec mx my =
  match mx with
  | Some x ->
    (match my with
     | Some y -> decide (decide_rel dec x y)
     | None -> false)
  | None -> (match my with
             | Some _ -> false
             | None -> true)

(** val option_bind : (__ -> __ option) -> __ option -> __ option **)

let option_bind f = function
| Some x -> f x
| None -> None

(** val option_fmap : (__ -> __) -> __ option -> __ option **)

let option_fmap =
  option_map

(** val option_union_with : ('a1, 'a1 option) coq_UnionWith **)

let option_union_with f mx my =
  match mx with
  | Some x -> (match my with
               | Some y -> f x y
               | None -> Some x)
  | None -> my

(** val option_intersection_with : ('a1, 'a1 option) coq_IntersectionWith **)

let option_intersection_with f mx my =
  match mx with
  | Some x -> (match my with
               | Some y -> f x y
               | None -> None)
  | None -> None
