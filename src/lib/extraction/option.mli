open Datatypes
open Base

type __ = Obj.t

val from_option : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_bind : (__ -> __ option) -> __ option -> __ option

val option_fmap : (__ -> __) -> __ option -> __ option

val option_union_with : ('a1, 'a1 option) coq_UnionWith

val option_intersection_with : ('a1, 'a1 option) coq_IntersectionWith
