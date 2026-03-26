open Base
open Option

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('k, 'a, 'm) coq_MapFold =
  __ -> ('k -> 'a -> __ -> __) -> __ -> 'm -> __

(** val map_fold :
    ('a1, 'a2, 'a3) coq_MapFold -> ('a1 -> 'a2 -> 'a4 -> 'a4) -> 'a4 -> 'a3
    -> 'a4 **)

let map_fold mapFold x x0 x1 =
  Obj.magic mapFold __ x x0 x1

(** val map_insert :
    ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a2, 'a3) coq_Insert **)

let map_insert h i x =
  partial_alter h (fun _ -> Some x) i

(** val map_singleton :
    ('a1, 'a2, 'a3) coq_PartialAlter -> 'a3 coq_Empty -> ('a1, 'a2, 'a3)
    coq_SingletonM **)

let map_singleton h h0 i x =
  insert (map_insert h) i x (empty h0)

(** val map_to_list :
    ('a1, 'a2, 'a3) coq_MapFold -> 'a3 -> ('a1 * 'a2) list **)

let map_to_list h =
  map_fold h (fun i x x0 -> (i, x) :: x0) []

(** val map_union_with : 'a1 coq_Merge -> ('a2, 'a1) coq_UnionWith **)

let map_union_with h f =
  merge h (union_with option_union_with f)

(** val map_intersection_with :
    'a1 coq_Merge -> ('a2, 'a1) coq_IntersectionWith **)

let map_intersection_with h f =
  merge h (intersection_with option_intersection_with f)

(** val map_union : 'a1 coq_Merge -> 'a1 coq_Union **)

let map_union h =
  union_with (map_union_with h) (fun x _ -> Some x)

(** val map_intersection : 'a1 coq_Merge -> 'a1 coq_Intersection **)

let map_intersection h =
  intersection_with (map_intersection_with h) (fun x _ -> Some x)
