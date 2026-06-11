open Datatypes
open Base
open Countable
open Decidable
open Mapset
open Numbers
open Option

type __ = Obj.t

type 'a gmap_dep_ne =
| GNode001 of 'a gmap_dep_ne
| GNode010 of 'a
| GNode011 of 'a * 'a gmap_dep_ne
| GNode100 of 'a gmap_dep_ne
| GNode101 of 'a gmap_dep_ne * 'a gmap_dep_ne
| GNode110 of 'a gmap_dep_ne * 'a
| GNode111 of 'a gmap_dep_ne * 'a * 'a gmap_dep_ne

type 'a gmap_dep =
| GEmpty
| GNodes of 'a gmap_dep_ne

type ('k, 'a) gmap = { gmap_car : 'a gmap_dep }

val gmap_dep_ne_eq_dec :
  ('a1, 'a1) coq_RelDecision -> ('a1 gmap_dep_ne, 'a1 gmap_dep_ne)
  coq_RelDecision

val gmap_dep_eq_dec :
  ('a1, 'a1) coq_RelDecision -> ('a1 gmap_dep, 'a1 gmap_dep) coq_RelDecision

val gmap_eq_dec :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a2, 'a2)
  coq_RelDecision -> (('a1, 'a2) gmap, ('a1, 'a2) gmap) coq_RelDecision

val coq_GNode :
  'a1 gmap_dep -> (__ * 'a1) option -> 'a1 gmap_dep -> 'a1 gmap_dep

val gmap_dep_ne_case :
  'a1 gmap_dep_ne -> ('a1 gmap_dep -> (__ * 'a1) option -> 'a1 gmap_dep ->
  'a2) -> 'a2

val gmap_dep_ne_lookup : Big_int_Z.big_int -> 'a1 gmap_dep_ne -> 'a1 option

val gmap_dep_lookup : Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1 option

val gmap_lookup :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
  gmap) coq_Lookup

val gmap_empty :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2) gmap coq_Empty

val gmap_dep_ne_singleton : Big_int_Z.big_int -> 'a1 -> 'a1 gmap_dep_ne

val gmap_partial_alter_aux :
  (Big_int_Z.big_int -> __ -> 'a1 gmap_dep_ne -> 'a1 gmap_dep) -> ('a1 option
  -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1 gmap_dep

val gmap_dep_ne_partial_alter :
  ('a1 option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep_ne -> 'a1
  gmap_dep

val gmap_dep_partial_alter :
  ('a1 option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1
  gmap_dep

val gmap_partial_alter :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
  gmap) coq_PartialAlter

val gmap_dep_ne_fmap : ('a1 -> 'a2) -> 'a1 gmap_dep_ne -> 'a2 gmap_dep_ne

val gmap_dep_fmap : ('a1 -> 'a2) -> 'a1 gmap_dep -> 'a2 gmap_dep

val gmap_fmap :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ -> __) -> ('a1, __)
  gmap -> ('a1, __) gmap

val gmap_dep_omap_aux :
  ('a1 gmap_dep_ne -> 'a2 gmap_dep) -> 'a1 gmap_dep -> 'a2 gmap_dep

val gmap_dep_ne_omap : ('a1 -> 'a2 option) -> 'a1 gmap_dep_ne -> 'a2 gmap_dep

val gmap_dep_omap : ('a1 -> 'a2 option) -> 'a1 gmap_dep -> 'a2 gmap_dep

val gmap_omap :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ -> __ option) ->
  ('a1, __) gmap -> ('a1, __) gmap

val gmap_merge_aux :
  ('a1 gmap_dep_ne -> 'a2 gmap_dep_ne -> 'a3 gmap_dep) -> ('a1 option -> 'a2
  option -> 'a3 option) -> 'a1 gmap_dep -> 'a2 gmap_dep -> 'a3 gmap_dep

val diag_None' :
  ('a1 option -> 'a2 option -> 'a3 option) -> (__ * 'a1) option -> (__ * 'a2)
  option -> (__ * 'a3) option

val gmap_dep_ne_merge :
  ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 gmap_dep_ne -> 'a2
  gmap_dep_ne -> 'a3 gmap_dep

val gmap_dep_merge :
  ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 gmap_dep -> 'a2 gmap_dep ->
  'a3 gmap_dep

val gmap_merge :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ option -> __ option
  -> __ option) -> ('a1, __) gmap -> ('a1, __) gmap -> ('a1, __) gmap

val gmap_fold_aux :
  (Big_int_Z.big_int -> 'a2 -> 'a1 gmap_dep_ne -> 'a2) -> Big_int_Z.big_int
  -> 'a2 -> 'a1 gmap_dep -> 'a2

val gmap_dep_ne_fold :
  (Big_int_Z.big_int -> 'a1 -> 'a2 -> 'a2) -> Big_int_Z.big_int -> 'a2 -> 'a1
  gmap_dep_ne -> 'a2

val gmap_dep_fold :
  (Big_int_Z.big_int -> 'a1 -> 'a2 -> 'a2) -> Big_int_Z.big_int -> 'a2 -> 'a1
  gmap_dep -> 'a2

val gmap_fold :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 -> 'a2 -> __ -> __)
  -> __ -> ('a1, 'a2) gmap -> __

type 'k gset = ('k, unit) gmap mapset'

val gset_singleton :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a1 gset)
  coq_Singleton

val gset_union :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> 'a1 gset coq_Union

val gset_intersection :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> 'a1 gset coq_Intersection

val gset_elements :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a1 gset)
  coq_Elements

val gset_elem_of_dec :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a1 gset)
  coq_RelDecision

val gset_subseteq_dec :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 gset, 'a1 gset)
  coq_RelDecision

val gset_dom :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (('a1, 'a2) gmap, 'a1
  gset) coq_Dom
