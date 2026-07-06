open Ast
open Datatypes
open List0
open ListDef
open ListUtil
open TypeAnnot

val lexp_subexps : 'a1 lexp -> 'a1 exp list

val update_lexp_subexps : 'a1 exp list -> 'a1 lexp -> 'a1 lexp * 'a1 exp list

type 'a zlexp_aux =
| LZ_id of id
| LZ_deref
| LZ_typ of typ * id
| LZ_tuple of 'a zlexp list
| LZ_vector_concat of 'a zlexp list
| LZ_vector of 'a zlexp
| LZ_vector_range of 'a zlexp
| LZ_field of 'a zlexp * id
and 'a zlexp =
| LZ_aux of 'a zlexp_aux * 'a annot

val lexp_to_z : 'a1 lexp -> 'a1 zlexp

val update_zlexp_subexps :
  'a1 exp list -> 'a1 zlexp -> 'a1 lexp option * 'a1 exp list

type var_type =
| Var_local
| Var_register

type 'v place =
| PL_id of id * var_type
| PL_register of 'v
| PL_vector of 'v place * 'v
| PL_vector_range of 'v place * 'v * 'v
| PL_field of 'v place * id

type 'v destructure =
| DL_tuple of 'v destructure list
| DL_vector_concat of (Types.vector_concat_split * 'v destructure) list
| DL_place of 'v place

module Typed :
 functor (Tannot:S) ->
 sig
  val zlexp_to_destructure :
    'a1 list -> Tannot.t zlexp -> 'a1 destructure option * 'a1 list
 end
