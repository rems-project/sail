open Base
open Decidable
open Fin_maps
open Option

type __ = Obj.t

type 'munit mapset' = { mapset_car : 'munit }

val mapset_singleton :
  (__ -> 'a2 coq_Empty) -> (__ -> ('a1, __, 'a2) coq_PartialAlter) -> ('a1,
  'a2 mapset') coq_Singleton

val mapset_union : 'a1 coq_Merge -> 'a1 mapset' coq_Union

val mapset_intersection : 'a1 coq_Merge -> 'a1 mapset' coq_Intersection

val mapset_eq_dec :
  ('a1, 'a1) coq_RelDecision -> ('a1 mapset', 'a1 mapset') coq_RelDecision

val mapset_elem_of_dec :
  (__ -> ('a1, __, 'a2) coq_Lookup) -> ('a1, 'a2 mapset') coq_RelDecision

val mapset_subseteq_dec :
  'a2 coq_FMap -> (__ -> ('a1, __, 'a2) coq_Lookup) -> (__ -> 'a2 coq_Empty)
  -> (__ -> ('a1, __, 'a2) coq_PartialAlter) -> 'a2 coq_OMap -> 'a2 coq_Merge
  -> (__ -> ('a1, __, 'a2) coq_MapFold) -> ('a1, 'a1) coq_RelDecision ->
  ('a2, 'a2) coq_RelDecision -> ('a2 mapset', 'a2 mapset') coq_RelDecision

val mapset_dom : 'a1 coq_FMap -> ('a1, 'a1 mapset') coq_Dom
