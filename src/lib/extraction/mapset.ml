open Datatypes
open Base
open Decidable
open Fin_maps
open List_monad
open Option

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'munit mapset' = { mapset_car : 'munit }

(** val mapset_singleton :
    (__ -> 'a2 coq_Empty) -> (__ -> ('a1, __, 'a2) coq_PartialAlter) -> ('a1,
    'a2 mapset') coq_Singleton **)

let mapset_singleton h1 h2 x =
  { mapset_car = (singletonM (map_singleton (Obj.magic h2 __) (h1 __)) x ()) }

(** val mapset_union : 'a1 coq_Merge -> 'a1 mapset' coq_Union **)

let mapset_union h4 x1 x2 =
  let { mapset_car = m1 } = x1 in
  let { mapset_car = m2 } = x2 in
  { mapset_car = (union (map_union h4) m1 m2) }

(** val mapset_intersection :
    'a1 coq_Merge -> 'a1 mapset' coq_Intersection **)

let mapset_intersection h4 x1 x2 =
  let { mapset_car = m1 } = x1 in
  let { mapset_car = m2 } = x2 in
  { mapset_car = (intersection (map_intersection h4) m1 m2) }

(** val mapset_elements :
    (__ -> ('a1, __, 'a2) coq_MapFold) -> ('a1, 'a2 mapset') coq_Elements **)

let mapset_elements h5 x =
  let { mapset_car = m } = x in
  fmap (Obj.magic (fun _ _ -> Coq_list.list_fmap)) fst
    (Obj.magic map_to_list (h5 __) m)

(** val mapset_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 mapset', 'a1 mapset') coq_RelDecision **)

let mapset_eq_dec eqDecision1 x1 x2 =
  let { mapset_car = m1 } = x1 in
  let { mapset_car = m2 } = x2 in decide (decide_rel eqDecision1 m1 m2)

(** val mapset_elem_of_dec :
    (__ -> ('a1, __, 'a2) coq_Lookup) -> ('a1, 'a2 mapset') coq_RelDecision **)

let mapset_elem_of_dec h0 x x0 =
  decide
    (decide_rel (Obj.magic option_eq_dec unit_eq_dec)
      (lookup (h0 __) x x0.mapset_car) (Some ()))

(** val mapset_subseteq_dec :
    'a2 coq_FMap -> (__ -> ('a1, __, 'a2) coq_Lookup) -> (__ -> 'a2
    coq_Empty) -> (__ -> ('a1, __, 'a2) coq_PartialAlter) -> 'a2 coq_OMap ->
    'a2 coq_Merge -> (__ -> ('a1, __, 'a2) coq_MapFold) -> ('a1, 'a1)
    coq_RelDecision -> ('a2, 'a2) coq_RelDecision -> ('a2 mapset', 'a2
    mapset') coq_RelDecision **)

let mapset_subseteq_dec _ _ _ _ _ h4 _ _ eqDecision1 x1 x2 =
  decide
    (decide_rel (mapset_eq_dec eqDecision1) (union (mapset_union h4) x1 x2)
      x2)

(** val mapset_dom : 'a1 coq_FMap -> ('a1, 'a1 mapset') coq_Dom **)

let mapset_dom h m =
  { mapset_car = (fmap h (fun _ -> ()) m) }
