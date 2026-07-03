open Ast
open BinInt
open BinNat
open Bit
open BitList
open Datatypes
open IdUtil
open Lattice
open List0
open ListDef
open ListUtil
open Nat0
open OptionUtil
open PatternMatch
open PeanoNat
open QArith_base
open Qcanon
open SailBase
open TypeAnnot
open ValueType
open Base
open Decidable
open Fin_maps
open Fin_sets
open Gmap
open List_basics
open Option

module Dom =
 functor (DZ:SAIL_INT) ->
 functor (Dbv:SAIL_BITS) ->
 functor (T:sig
  val unsigned : Dbv.t -> DZ.t

  val signed : Dbv.t -> DZ.t

  val zeros : Big_int_Z.big_int -> DZ.t -> Dbv.t

  val ones : Big_int_Z.big_int -> DZ.t -> Dbv.t

  val zero_extend : Big_int_Z.big_int -> Dbv.t -> DZ.t -> Dbv.t

  val sign_extend : Big_int_Z.big_int -> Dbv.t -> DZ.t -> Dbv.t

  val count_leading_zeros : Dbv.t -> DZ.t

  val count_trailing_zeros : Dbv.t -> DZ.t

  val bits_length : Dbv.t -> DZ.t
 end) ->
 struct
  module DZP = DomainProperties(Z)(DZ)

  module DbvP = DomainProperties(Bits)(Dbv)

  type value =
  | V_bitvector of Dbv.t
  | V_vector of value list
  | V_list of value list
  | V_int of DZ.t
  | V_real of coq_Qc
  | V_bool of bool
  | V_tuple of value list
  | V_unit
  | V_string of string
  | V_ref of id_aux
  | V_member of id_aux gset
  | V_ctor of (id_aux, value list) gmap
  | V_record of (id_aux, value) gmap
  | V_top
  | V_bot

  (** val value_rect :
      (Dbv.t -> 'a1) -> (value list -> 'a1) -> (value list -> 'a1) -> (DZ.t
      -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value list -> 'a1) ->
      'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux gset -> 'a1) ->
      ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value) gmap -> 'a1) ->
      'a1 -> 'a1 -> value -> 'a1 **)

  let value_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | V_bitvector t0 -> f t0
  | V_vector l -> f0 l
  | V_list l -> f1 l
  | V_int t0 -> f2 t0
  | V_real q -> f3 q
  | V_bool b -> f4 b
  | V_tuple l -> f5 l
  | V_unit -> f6
  | V_string s -> f7 s
  | V_ref i -> f8 i
  | V_member g -> f9 g
  | V_ctor g -> f10 g
  | V_record g -> f11 g
  | V_top -> f12
  | V_bot -> f13

  (** val value_rec :
      (Dbv.t -> 'a1) -> (value list -> 'a1) -> (value list -> 'a1) -> (DZ.t
      -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value list -> 'a1) ->
      'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux gset -> 'a1) ->
      ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value) gmap -> 'a1) ->
      'a1 -> 'a1 -> value -> 'a1 **)

  let value_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | V_bitvector t0 -> f t0
  | V_vector l -> f0 l
  | V_list l -> f1 l
  | V_int t0 -> f2 t0
  | V_real q -> f3 q
  | V_bool b -> f4 b
  | V_tuple l -> f5 l
  | V_unit -> f6
  | V_string s -> f7 s
  | V_ref i -> f8 i
  | V_member g -> f9 g
  | V_ctor g -> f10 g
  | V_record g -> f11 g
  | V_top -> f12
  | V_bot -> f13

  (** val mk_ctor : id_aux -> value list -> value **)

  let mk_ctor s args =
    V_ctor
      (singletonM
        (map_singleton (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable)
          (gmap_empty Aux.eq_eqdec Aux.id_aux_countable))
        s args)

  (** val mk_member : id_aux -> value **)

  let mk_member s =
    V_member (singleton (gset_singleton Aux.eq_eqdec Aux.id_aux_countable) s)

  (** val is_unit : value -> bool **)

  let is_unit = function
  | V_unit -> true
  | _ -> false

  (** val is_true : value -> bool **)

  let is_true = function
  | V_bool b -> b
  | _ -> false

  (** val is_false : value -> bool **)

  let is_false = function
  | V_bool b -> if b then false else true
  | _ -> false

  type t = value

  (** val top : value **)

  let top =
    V_top

  (** val bot : t **)

  let bot =
    V_bot

  (** val value_length : value -> value **)

  let value_length = function
  | V_bitvector bv -> V_int (T.bits_length bv)
  | V_vector vs -> V_int (DZ.abst (Z.of_nat (length vs)))
  | V_list vs -> V_int (DZ.abst (Z.of_nat (length vs)))
  | _ -> V_bot

  (** val mk_bitvector' : value list -> Dbv.t option **)

  let mk_bitvector' vs =
    fold_left (fun acc v ->
      match acc with
      | Some acc' ->
        (match v with
         | V_bitvector bv ->
           Some (Dbv.append acc' (Dbv.meet bv Dbv.unknown_bit))
         | _ -> None)
      | None -> None) vs (Some Dbv.zwbv)

  (** val mk_bitvector : value list -> value **)

  let mk_bitvector vs =
    match mk_bitvector' vs with
    | Some bv -> V_bitvector bv
    | None -> V_bot

  (** val vdepth : value -> Big_int_Z.big_int **)

  let rec vdepth = function
  | V_vector vs ->
    add (fold_right max Big_int_Z.zero_big_int (map vdepth vs))
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  | V_list vs ->
    add (fold_right max Big_int_Z.zero_big_int (map vdepth vs))
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  | V_tuple vs ->
    add (fold_right max Big_int_Z.zero_big_int (map vdepth vs))
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  | V_ctor m ->
    add
      (map_fold (fun _ -> gmap_fold Aux.eq_eqdec Aux.id_aux_countable)
        (fun _ vs acc -> fold_right max acc (map vdepth vs))
        Big_int_Z.zero_big_int m)
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  | V_record m ->
    add
      (map_fold (fun _ -> gmap_fold Aux.eq_eqdec Aux.id_aux_countable)
        (fun _ v0 acc -> max acc (vdepth v0)) Big_int_Z.zero_big_int m)
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  | _ -> Big_int_Z.zero_big_int

  (** val key_inter :
      (id_aux, 'a1) gmap -> (id_aux, 'a1) gmap -> id_aux list **)

  let key_inter m1 m2 =
    map fst
      (filter (fun _ -> Coq_list.list_filter)
        (uncurry_dec (fun x _ ->
          coq_Is_true_dec
            (bool_decide
              (decide_rel
                (gset_elem_of_dec Aux.eq_eqdec Aux.id_aux_countable) x
                (dom (gset_dom Aux.eq_eqdec Aux.id_aux_countable) m2)))))
        (map_to_list (fun _ -> gmap_fold Aux.eq_eqdec Aux.id_aux_countable)
          m1))

  (** val ctor_compat :
      (id_aux, value list) gmap -> (id_aux, value list) gmap -> bool **)

  let ctor_compat x y =
    forallb (fun k ->
      let o = lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) k x in
      let o0 = lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) k y in
      (match o with
       | Some vx ->
         (match o0 with
          | Some vy -> Nat.eqb (length vx) (length vy)
          | None -> true)
       | None -> true))
      (key_inter x y)

  (** val same_or : 'a1 coq_EqDecb -> t -> ('a1 -> t) -> 'a1 -> 'a1 -> t **)

  let same_or h e v x y =
    if h.eqb x y then v x else e

  (** val join : value -> value -> value **)

  let rec join v_UU2081_ v_UU2082_ =
    match v_UU2081_ with
    | V_bitvector bv_UU2081_ ->
      (match v_UU2082_ with
       | V_bitvector bv_UU2082_ ->
         V_bitvector (Dbv.join bv_UU2081_ bv_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_vector vs_UU2081_ ->
      (match v_UU2082_ with
       | V_vector vs_UU2082_ ->
         from_option (fun x -> V_vector x) V_top
           (zip_with_opt join vs_UU2081_ vs_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_list vs_UU2081_ ->
      (match v_UU2082_ with
       | V_list vs_UU2082_ ->
         from_option (fun x -> V_list x) V_top
           (zip_with_opt join vs_UU2081_ vs_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_int i_UU2081_ ->
      (match v_UU2082_ with
       | V_int i_UU2082_ -> V_int (DZ.join i_UU2081_ i_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_real q_UU2081_ ->
      (match v_UU2082_ with
       | V_real q_UU2082_ ->
         same_or coq_Qc_eqdecb V_top (fun x -> V_real x) q_UU2081_ q_UU2082_
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_bool b_UU2081_ ->
      (match v_UU2082_ with
       | V_bool b_UU2082_ ->
         same_or bool_eqdecb V_top (fun x -> V_bool x) b_UU2081_ b_UU2082_
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_tuple vs_UU2081_ ->
      (match v_UU2082_ with
       | V_tuple vs_UU2082_ ->
         from_option (fun x -> V_tuple x) V_top
           (zip_with_opt join vs_UU2081_ vs_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_unit ->
      (match v_UU2082_ with
       | V_unit -> V_unit
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_string s_UU2081_ ->
      (match v_UU2082_ with
       | V_string s_UU2082_ ->
         same_or string_eqdecb V_top (fun x -> V_string x) s_UU2081_ s_UU2082_
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_ref id_UU2081_ ->
      (match v_UU2082_ with
       | V_ref id_UU2082_ ->
         same_or Aux.id_aux_eqdecb V_top (fun x -> V_ref x) id_UU2081_
           id_UU2082_
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_member ids_UU2081_ ->
      (match v_UU2082_ with
       | V_member ids_UU2082_ ->
         V_member
           (union (gset_union Aux.eq_eqdec Aux.id_aux_countable) ids_UU2081_
             ids_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_ctor m_UU2081_ ->
      (match v_UU2082_ with
       | V_ctor m_UU2082_ ->
         if ctor_compat m_UU2081_ m_UU2082_
         then V_ctor
                (merge
                  (Obj.magic (fun _ _ _ ->
                    gmap_merge Aux.eq_eqdec Aux.id_aux_countable))
                  (option_join (zip_with join)) m_UU2081_ m_UU2082_)
         else V_top
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_record m_UU2081_ ->
      (match v_UU2082_ with
       | V_record m_UU2082_ ->
         V_record
           (merge
             (Obj.magic (fun _ _ _ ->
               gmap_merge Aux.eq_eqdec Aux.id_aux_countable))
             (option_join join) m_UU2081_ m_UU2082_)
       | V_bot -> v_UU2081_
       | _ -> V_top)
    | V_top -> (match v_UU2082_ with
                | V_bot -> v_UU2081_
                | _ -> V_top)
    | V_bot -> v_UU2082_

  (** val meet : value -> value -> value **)

  let rec meet v_UU2081_ v_UU2082_ =
    match v_UU2081_ with
    | V_bitvector bv_UU2081_ ->
      (match v_UU2082_ with
       | V_bitvector bv_UU2082_ ->
         V_bitvector (Dbv.meet bv_UU2081_ bv_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_vector vs_UU2081_ ->
      (match v_UU2082_ with
       | V_vector vs_UU2082_ ->
         from_option (fun x -> V_vector x) V_bot
           (zip_with_opt meet vs_UU2081_ vs_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_list vs_UU2081_ ->
      (match v_UU2082_ with
       | V_list vs_UU2082_ ->
         from_option (fun x -> V_list x) V_bot
           (zip_with_opt meet vs_UU2081_ vs_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_int i_UU2081_ ->
      (match v_UU2082_ with
       | V_int i_UU2082_ -> V_int (DZ.meet i_UU2081_ i_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_real q_UU2081_ ->
      (match v_UU2082_ with
       | V_real q_UU2082_ ->
         same_or coq_Qc_eqdecb V_bot (fun x -> V_real x) q_UU2081_ q_UU2082_
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_bool b_UU2081_ ->
      (match v_UU2082_ with
       | V_bool b_UU2082_ ->
         same_or bool_eqdecb V_bot (fun x -> V_bool x) b_UU2081_ b_UU2082_
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_tuple vs_UU2081_ ->
      (match v_UU2082_ with
       | V_tuple vs_UU2082_ ->
         from_option (fun x -> V_tuple x) V_bot
           (zip_with_opt meet vs_UU2081_ vs_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_unit ->
      (match v_UU2082_ with
       | V_unit -> V_unit
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_string s_UU2081_ ->
      (match v_UU2082_ with
       | V_string s_UU2082_ ->
         same_or string_eqdecb V_bot (fun x -> V_string x) s_UU2081_ s_UU2082_
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_ref id_UU2081_ ->
      (match v_UU2082_ with
       | V_ref id_UU2082_ ->
         same_or Aux.id_aux_eqdecb V_bot (fun x -> V_ref x) id_UU2081_
           id_UU2082_
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_member ids_UU2081_ ->
      (match v_UU2082_ with
       | V_member ids_UU2082_ ->
         V_member
           (intersection
             (gset_intersection Aux.eq_eqdec Aux.id_aux_countable)
             ids_UU2081_ ids_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_ctor m_UU2081_ ->
      (match v_UU2082_ with
       | V_ctor m_UU2082_ ->
         V_ctor
           (merge
             (Obj.magic (fun _ _ _ ->
               gmap_merge Aux.eq_eqdec Aux.id_aux_countable))
             (fun o_UU2081_ o_UU2082_ ->
             match o_UU2081_ with
             | Some l_UU2081_ ->
               (match o_UU2082_ with
                | Some l_UU2082_ ->
                  if Nat.eqb (length l_UU2081_) (length l_UU2082_)
                  then Some (zip_with meet l_UU2081_ l_UU2082_)
                  else None
                | None -> None)
             | None -> None) m_UU2081_ m_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_record m_UU2081_ ->
      (match v_UU2082_ with
       | V_record m_UU2082_ ->
         V_record
           (merge
             (Obj.magic (fun _ _ _ ->
               gmap_merge Aux.eq_eqdec Aux.id_aux_countable))
             (option_map2 meet) m_UU2081_ m_UU2082_)
       | V_top -> v_UU2081_
       | _ -> V_bot)
    | V_top -> v_UU2082_
    | V_bot -> (match v_UU2082_ with
                | V_top -> v_UU2081_
                | _ -> V_bot)

  (** val leb : value -> value -> bool **)

  let rec leb x y =
    match x with
    | V_bitvector xbv ->
      (match y with
       | V_bitvector ybv -> Dbv.leb xbv ybv
       | V_top -> true
       | _ -> false)
    | V_vector xs ->
      (match y with
       | V_vector ys -> list_eqb leb xs ys
       | V_top -> true
       | _ -> false)
    | V_list xs ->
      (match y with
       | V_list ys -> list_eqb leb xs ys
       | V_top -> true
       | _ -> false)
    | V_int xi ->
      (match y with
       | V_int yi -> DZ.leb xi yi
       | V_top -> true
       | _ -> false)
    | V_real xq ->
      (match y with
       | V_real yq -> coq_Qc_eqdecb.eqb xq yq
       | V_top -> true
       | _ -> false)
    | V_bool xb ->
      (match y with
       | V_bool yb -> bool_eqdecb.eqb xb yb
       | V_top -> true
       | _ -> false)
    | V_tuple xs ->
      (match y with
       | V_tuple ys -> list_eqb leb xs ys
       | V_top -> true
       | _ -> false)
    | V_unit -> (match y with
                 | V_unit -> true
                 | V_top -> true
                 | _ -> false)
    | V_string xstr ->
      (match y with
       | V_string ystr -> string_eqdecb.eqb xstr ystr
       | V_top -> true
       | _ -> false)
    | V_ref xid ->
      (match y with
       | V_ref yid -> Aux.id_aux_eqdecb.eqb xid yid
       | V_top -> true
       | _ -> false)
    | V_member xs ->
      (match y with
       | V_member ys ->
         if decide
              (decide_rel
                (gset_subseteq_dec Aux.eq_eqdec Aux.id_aux_countable) xs ys)
         then true
         else false
       | V_top -> true
       | _ -> false)
    | V_ctor xm ->
      (match y with
       | V_ctor ym ->
         if ctor_compat xm ym
         then map_fold (fun _ -> gmap_fold Aux.eq_eqdec Aux.id_aux_countable)
                (fun k xs b ->
                (&&) b
                  (match lookup
                           (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) k
                           ym with
                   | Some ys -> list_eqb leb xs ys
                   | None -> false))
                true xm
         else false
       | V_top -> true
       | _ -> false)
    | V_record xm ->
      (match y with
       | V_record ym ->
         map_fold (fun _ -> gmap_fold Aux.eq_eqdec Aux.id_aux_countable)
           (fun k x0 b ->
           (&&) b
             (match lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) k
                      ym with
              | Some y0 -> leb x0 y0
              | None -> false))
           true xm
       | V_top -> true
       | _ -> false)
    | V_top -> (match y with
                | V_top -> true
                | _ -> false)
    | V_bot -> true

  (** val abst : Ast.value -> value **)

  let rec abst = function
  | Ast.V_bitvector bv -> V_bitvector (Dbv.abst (Bit.Bits.to_bvn bv))
  | Ast.V_vector xs -> V_vector (map abst xs)
  | Ast.V_list xs -> V_list (map abst xs)
  | Ast.V_int i -> V_int (DZ.abst i)
  | Ast.V_real q -> V_real (coq_Q2Qc q)
  | Ast.V_bool b -> V_bool b
  | Ast.V_tuple xs -> V_tuple (map abst xs)
  | Ast.V_unit -> V_unit
  | Ast.V_string str -> V_string str
  | Ast.V_ref id -> V_ref (Aux.unwrap id)
  | Ast.V_member id ->
    V_member
      (singleton (gset_singleton Aux.eq_eqdec Aux.id_aux_countable)
        (Aux.unwrap id))
  | Ast.V_ctor (id, xs) ->
    V_ctor
      (singletonM
        (map_singleton (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable)
          (gmap_empty Aux.eq_eqdec Aux.id_aux_countable))
        (Aux.unwrap id) (map abst xs))
  | Ast.V_record fields ->
    V_record
      (Coq_list.foldl (fun m pat0 ->
        let (k, v) = pat0 in
        insert
          (map_insert (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable))
          (Aux.unwrap k) (abst v) m)
        (empty (gmap_empty Aux.eq_eqdec Aux.id_aux_countable)) fields)

  (** val of_lit : lit -> value **)

  let of_lit l =
    abst (value_of_lit l)

  (** val lookup_field : value -> id_aux -> value **)

  let lookup_field r name =
    match r with
    | V_record m ->
      from_option (fun x -> x) V_bot
        (lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) name m)
    | _ -> V_bot

  (** val int_concrete : DZ.t -> Big_int_Z.big_int option **)

  let int_concrete =
    DZ.concrete

  (** val bv_slice :
      value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value **)

  let bv_slice v s m =
    match v with
    | V_bitvector bv -> V_bitvector (Dbv.slice bv s m)
    | _ -> V_top

  (** val set_field : value -> id_aux -> value -> value **)

  let set_field r k v =
    match r with
    | V_record m ->
      V_record
        (insert
          (map_insert (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable))
          k v m)
    | V_top ->
      V_record
        (insert
          (map_insert (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable))
          k v (empty (gmap_empty Aux.eq_eqdec Aux.id_aux_countable)))
    | _ -> V_top

  (** val vector_update :
      value list -> Big_int_Z.big_int -> value -> value list **)

  let rec vector_update vs i v =
    match vs with
    | [] -> []
    | x :: rest ->
      ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
         (fun _ -> v :: rest)
         (fun n -> x :: (vector_update rest n v))
         i)

  (** val set_bv_range :
      value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value -> value **)

  let set_bv_range base hi lo new0 =
    match base with
    | V_bitvector bv_base ->
      (match new0 with
       | V_bitvector bv_new ->
         (match DZ.concrete (T.bits_length bv_base) with
          | Some n_z ->
            if (&&) (Z.leb Big_int_Z.zero_big_int lo)
                 ((&&) (Z.leb lo hi) (Z.ltb hi n_z))
            then let n_N = Z.to_N n_z in
                 let lo_N = Z.to_N lo in
                 let hi_N = Z.to_N hi in
                 let high_start = N.add hi_N Big_int_Z.unit_big_int in
                 let high_width = N.sub n_N high_start in
                 let high_part = Dbv.slice bv_base high_start high_width in
                 let low_part = Dbv.slice bv_base Big_int_Z.zero_big_int lo_N
                 in
                 V_bitvector
                 (Dbv.append high_part (Dbv.append bv_new low_part))
            else V_top
          | None -> V_top)
       | _ -> V_top)
    | _ -> V_top

  (** val get_vector_elem : value -> Big_int_Z.big_int -> value **)

  let get_vector_elem xs i =
    match xs with
    | V_vector vs ->
      let n = Z.of_nat (length vs) in
      if (&&) (Z.leb Big_int_Z.zero_big_int i) (Z.ltb i n)
      then (match nth_error vs
                    (Z.to_nat (Z.sub (Z.sub n Big_int_Z.unit_big_int) i)) with
            | Some x -> x
            | None -> V_top)
      else V_top
    | _ -> V_top

  (** val set_vector_elem : value -> Big_int_Z.big_int -> value -> value **)

  let set_vector_elem xs i v =
    match xs with
    | V_bitvector _ -> set_bv_range xs i i v
    | V_vector vs ->
      let n = Z.of_nat (length vs) in
      if (&&) (Z.leb Big_int_Z.zero_big_int i) (Z.ltb i n)
      then V_vector
             (vector_update vs
               (Z.to_nat (Z.sub (Z.sub n Big_int_Z.unit_big_int) i)) v)
      else V_top
    | _ -> V_top

  module Matching =
   functor (Tannot:S) ->
   struct
    (** val match_bitvector_lit : bit list -> Dbv.t -> value match_result **)

    let match_bitvector_lit lit_bs bv =
      let lit_bv = Dbv.abst (Bit.Bits.to_bvn lit_bs) in
      if Dbv.leb lit_bv bv
      then if Dbv.leb bv lit_bv
           then simple_match
           else MaybeMatched empty_bindings
      else Unmatched

    (** val pattern_match_literal : lit -> value -> value match_result **)

    let pattern_match_literal l v =
      let L_aux (aux, _) = l in
      (match aux with
       | L_unit -> (match v with
                    | V_unit -> simple_match
                    | _ -> Unmatched)
       | L_true ->
         (match v with
          | V_bool b -> if b then simple_match else Unmatched
          | _ -> Unmatched)
       | L_false ->
         (match v with
          | V_bool b -> if b then Unmatched else simple_match
          | _ -> Unmatched)
       | L_num n ->
         (match v with
          | V_int m ->
            if DZ.leb (DZ.abst n) m
            then if DZ.leb m (DZ.abst n)
                 then simple_match
                 else MaybeMatched empty_bindings
            else Unmatched
          | _ -> Unmatched)
       | L_hex s ->
         (match v with
          | V_bitvector vs -> match_bitvector_lit (of_hex_lit s) vs
          | _ -> Unmatched)
       | L_bin s ->
         (match v with
          | V_bitvector vs -> match_bitvector_lit (of_bin_lit s) vs
          | _ -> Unmatched)
       | L_string s1 ->
         (match v with
          | V_string s2 -> simple_match_when ((=) s1 s2)
          | _ -> Unmatched)
       | L_real r1 ->
         (match v with
          | V_real r2 -> simple_match_when (coq_Qeq_bool r1 r2.this)
          | _ -> Unmatched))

    (** val pattern_match : Tannot.t pat -> value -> value match_result **)

    let rec pattern_match p v =
      let P_aux (aux, _) = p in
      (match aux with
       | P_lit lit0 -> pattern_match_literal lit0 v
       | P_as (p', id) -> add_match id (Complete v) (pattern_match p' v)
       | P_typ (_, p') -> pattern_match p' v
       | P_id id ->
         let P_aux (_, annot) = p in
         (match Tannot.get_id_type (snd annot) id with
          | Types.Enum_member ->
            (match v with
             | V_member ids ->
               if bool_decide
                    (decide_rel
                      (gset_elem_of_dec Aux.eq_eqdec Aux.id_aux_countable)
                      (Aux.unwrap id) ids)
               then if Nat.eqb
                         (size
                           (set_size
                             (gset_elements Aux.eq_eqdec Aux.id_aux_countable))
                           ids)
                         (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
                    then simple_match
                    else MaybeMatched empty_bindings
               else Unmatched
             | V_top -> MaybeMatched empty_bindings
             | _ -> Unmatched)
          | _ -> add_match id (Complete v) simple_match)
       | P_var (p', _) -> pattern_match p' v
       | P_app (ctor, ps) ->
         (match v with
          | V_ctor m ->
            (match lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable)
                     (Aux.unwrap ctor) m with
             | Some vs ->
               if Nat.eqb (length ps) (length vs)
               then let inner =
                      fst
                        (fold_left (fun acc p0 ->
                          let (r, vs0) = acc in
                          (match vs0 with
                           | [] -> (Unmatched, [])
                           | v0 :: rest ->
                             ((merge_match_result r (pattern_match p0 v0)),
                               rest)))
                          ps (simple_match, vs))
                    in
                    if Nat.eqb
                         (size
                           (map_size (fun _ ->
                             gmap_fold Aux.eq_eqdec Aux.id_aux_countable))
                           m)
                         (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
                    then inner
                    else (match inner with
                          | Matched b -> MaybeMatched b
                          | _ -> inner)
               else Unmatched
             | None -> Unmatched)
          | V_top -> simple_match
          | _ -> Unmatched)
       | P_vector ps ->
         (match v with
          | V_bitvector bv ->
            let n = length ps in
            fst
              (fold_left (fun acc p0 ->
                let (prev, off) = acc in
                let off' =
                  Nat.sub off (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
                in
                let piece = V_bitvector
                  (Dbv.slice bv (N.of_nat off')
                    (N.of_nat (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
                in
                ((merge_match_result prev (pattern_match p0 piece)), off'))
                ps (simple_match, n))
          | V_vector vs ->
            if Nat.eqb (length ps) (length vs)
            then fst
                   (fold_left (fun acc p0 ->
                     let (prev, vs0) = acc in
                     (match vs0 with
                      | [] -> (Unmatched, [])
                      | v0 :: rest ->
                        ((merge_match_result prev (pattern_match p0 v0)),
                          rest)))
                     ps (simple_match, vs))
            else Unmatched
          | V_top -> simple_match
          | _ -> Unmatched)
       | P_vector_concat ps ->
         (match v with
          | V_bitvector bv ->
            let total =
              fold_left (fun acc p0 ->
                let P_aux (_, ann) = p0 in
                (match Tannot.get_split (snd ann) with
                 | Types.No_split -> acc
                 | Types.Split n -> Nat.add acc n))
                ps Big_int_Z.zero_big_int
            in
            fst
              (fold_left (fun acc p0 ->
                let (prev, off) = acc in
                let P_aux (_, ann) = p0 in
                (match Tannot.get_split (snd ann) with
                 | Types.No_split -> (Unmatched, off)
                 | Types.Split s ->
                   let off' = Nat.sub off s in
                   let piece = V_bitvector
                     (Dbv.slice bv (N.of_nat off') (N.of_nat s))
                   in
                   ((merge_match_result prev (pattern_match p0 piece)), off')))
                ps (simple_match, total))
          | V_top -> simple_match
          | _ -> Unmatched)
       | P_vector_subrange (id, n, m) ->
         add_match id (Partial (Non_empty (((v, n), m), []))) simple_match
       | P_tuple ps ->
         (match v with
          | V_tuple vs ->
            if Nat.eqb (length ps) (length vs)
            then fst
                   (fold_left (fun acc p0 ->
                     let (r, vs0) = acc in
                     (match vs0 with
                      | [] -> (Unmatched, [])
                      | v0 :: rest ->
                        ((merge_match_result r (pattern_match p0 v0)), rest)))
                     ps (simple_match, vs))
            else Unmatched
          | V_unit -> (match ps with
                       | [] -> simple_match
                       | _ :: _ -> Unmatched)
          | _ -> simple_match)
       | P_list ps ->
         (match v with
          | V_list vs ->
            if Nat.eqb (length ps) (length vs)
            then fst
                   (fold_left (fun acc p0 ->
                     let (r, vs0) = acc in
                     (match vs0 with
                      | [] -> (Unmatched, [])
                      | v0 :: rest ->
                        ((merge_match_result r (pattern_match p0 v0)), rest)))
                     ps (simple_match, vs))
            else Unmatched
          | V_top -> simple_match
          | _ -> Unmatched)
       | P_cons (head_pat, tail_pat) ->
         (match v with
          | V_list l ->
            (match l with
             | [] -> Unmatched
             | h :: t0 ->
               merge_match_result (pattern_match head_pat h)
                 (pattern_match tail_pat (V_list t0)))
          | V_top -> simple_match
          | _ -> Unmatched)
       | P_struct (_, field_pats, _) ->
         (match v with
          | V_record m ->
            fold_left (fun acc fp ->
              let (field, fpat) = fp in
              (match lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable)
                       (Aux.unwrap field) m with
               | Some fv -> merge_match_result acc (pattern_match fpat fv)
               | None -> Unmatched))
              field_pats simple_match
          | V_top -> simple_match
          | _ -> Unmatched)
       | _ -> simple_match)
   end

  (** val complete_partial :
      ((t * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> t **)

  let complete_partial = function
  | Non_empty (p, rest) ->
    let (p0, m1) = p in
    let (v1, n1) = p0 in
    let (max0, _) =
      fold_left (fun range pvalue ->
        let (max0, min0) = range in
        let (p1, m) = pvalue in
        let (_, n) = p1 in
        ((Z.max max0 (Z.max n m)), (Z.min min0 (Z.min n m)))) rest
        ((Z.max n1 m1), (Z.min n1 m1))
    in
    let len = Z.succ max0 in
    let zeros0 = V_bitvector
      (Dbv.abst (Bit.Bits.to_bvn (repeat B0 (Z.to_nat len))))
    in
    fold_left (fun bv pvalue ->
      let (y, m) = pvalue in
      let (slice0, n) = y in set_bv_range bv (Z.max n m) (Z.min n m) slice0)
      (((v1, n1), m1) :: rest) zeros0

  (** val complete : t binding -> t **)

  let complete = function
  | Complete v -> v
  | Partial vs -> complete_partial vs
 end
