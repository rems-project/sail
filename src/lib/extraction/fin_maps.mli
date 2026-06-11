open Base
open Option

type __ = Obj.t

type ('k, 'a, 'm) coq_MapFold =
  __ -> ('k -> 'a -> __ -> __) -> __ -> 'm -> __

val map_fold :
  ('a1, 'a2, 'a3) coq_MapFold -> ('a1 -> 'a2 -> 'a4 -> 'a4) -> 'a4 -> 'a3 ->
  'a4

val map_insert :
  ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a2, 'a3) coq_Insert

val map_singleton :
  ('a1, 'a2, 'a3) coq_PartialAlter -> 'a3 coq_Empty -> ('a1, 'a2, 'a3)
  coq_SingletonM

val map_size : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 coq_Size

val map_to_list : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 -> ('a1 * 'a2) list

val map_union_with : 'a1 coq_Merge -> ('a2, 'a1) coq_UnionWith

val map_intersection_with : 'a1 coq_Merge -> ('a2, 'a1) coq_IntersectionWith

val map_union : 'a1 coq_Merge -> 'a1 coq_Union

val map_intersection : 'a1 coq_Merge -> 'a1 coq_Intersection
