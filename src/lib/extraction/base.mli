
type __ = Obj.t

type coq_Decision = bool

val decide : coq_Decision -> bool

type ('a, 'b) coq_RelDecision = 'a -> 'b -> coq_Decision

val decide_rel : ('a1, 'a2) coq_RelDecision -> 'a1 -> 'a2 -> coq_Decision

val zip_with : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

type 'a coq_Empty = 'a

val empty : 'a1 coq_Empty -> 'a1

type 'a coq_Union = 'a -> 'a -> 'a

val union : 'a1 coq_Union -> 'a1 -> 'a1 -> 'a1

type 'a coq_Intersection = 'a -> 'a -> 'a

val intersection : 'a1 coq_Intersection -> 'a1 -> 'a1 -> 'a1

type ('a, 'b) coq_Singleton = 'a -> 'b

val singleton : ('a1, 'a2) coq_Singleton -> 'a1 -> 'a2

type 'm coq_MBind = __ -> __ -> (__ -> 'm) -> 'm -> 'm

val mbind : 'a1 coq_MBind -> ('a2 -> 'a1) -> 'a1 -> 'a1

type 'm coq_FMap = __ -> __ -> (__ -> __) -> 'm -> 'm

val fmap : 'a1 coq_FMap -> ('a2 -> 'a3) -> 'a1 -> 'a1

type 'm coq_OMap = __ -> __ -> (__ -> __ option) -> 'm -> 'm

type ('k, 'a, 'm) coq_Lookup = 'k -> 'm -> 'a option

val lookup : ('a1, 'a2, 'a3) coq_Lookup -> 'a1 -> 'a3 -> 'a2 option

type ('k, 'a, 'm) coq_SingletonM = 'k -> 'a -> 'm

val singletonM : ('a1, 'a2, 'a3) coq_SingletonM -> 'a1 -> 'a2 -> 'a3

type ('k, 'a, 'm) coq_Insert = 'k -> 'a -> 'm -> 'm

val insert : ('a1, 'a2, 'a3) coq_Insert -> 'a1 -> 'a2 -> 'a3 -> 'a3

type ('k, 'a, 'm) coq_PartialAlter =
  ('a option -> 'a option) -> 'k -> 'm -> 'm

val partial_alter :
  ('a1, 'a2, 'a3) coq_PartialAlter -> ('a2 option -> 'a2 option) -> 'a1 ->
  'a3 -> 'a3

type 'm coq_Merge =
  __ -> __ -> __ -> (__ option -> __ option -> __ option) -> 'm -> 'm -> 'm

val merge :
  'a1 coq_Merge -> ('a2 option -> 'a3 option -> 'a4 option) -> 'a1 -> 'a1 ->
  'a1

type ('a, 'm) coq_UnionWith = ('a -> 'a -> 'a option) -> 'm -> 'm -> 'm

val union_with :
  ('a1, 'a2) coq_UnionWith -> ('a1 -> 'a1 -> 'a1 option) -> 'a2 -> 'a2 -> 'a2

type ('a, 'm) coq_IntersectionWith = ('a -> 'a -> 'a option) -> 'm -> 'm -> 'm

val intersection_with :
  ('a1, 'a2) coq_IntersectionWith -> ('a1 -> 'a1 -> 'a1 option) -> 'a2 -> 'a2
  -> 'a2
