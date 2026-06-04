open AbsBitvector
open Ast
open BinInt
open Bit
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
open Qcanon
open SailBase
open ValueType
open Base
open Decidable
open Fin_maps
open Gmap
open List_basics
open Option

module Dom =
 functor (DZ:sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : Z.t -> t
 end) ->
 functor (Dbv:sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : AbsBitvector.Bits.t -> t
 end) ->
 struct
  module DZP = DomainProperties(Z)(DZ)

  module DbvP = DomainProperties(AbsBitvector.Bits)(Dbv)

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

  (** val _UU03b1_ : Ast.value -> value **)

  let rec _UU03b1_ = function
  | Ast.V_bitvector bv -> V_bitvector (Dbv._UU03b1_ (Bits.to_bvn bv))
  | Ast.V_vector xs -> V_vector (map _UU03b1_ xs)
  | Ast.V_list xs -> V_list (map _UU03b1_ xs)
  | Ast.V_int i -> V_int (DZ._UU03b1_ i)
  | Ast.V_real q -> V_real (coq_Q2Qc q)
  | Ast.V_bool b -> V_bool b
  | Ast.V_tuple xs -> V_tuple (map _UU03b1_ xs)
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
        (Aux.unwrap id) (map _UU03b1_ xs))
  | Ast.V_record fields ->
    V_record
      (Coq_list.foldl (fun m pat ->
        let (k, v) = pat in
        insert
          (map_insert (gmap_partial_alter Aux.eq_eqdec Aux.id_aux_countable))
          (Aux.unwrap k) (_UU03b1_ v) m)
        (empty (gmap_empty Aux.eq_eqdec Aux.id_aux_countable)) fields)

  (** val of_lit : lit -> value **)

  let of_lit l =
    _UU03b1_ (value_of_lit l)

  (** val lookup_field : value -> id_aux -> value **)

  let lookup_field r name =
    match r with
    | V_record m ->
      from_option (fun x -> x) V_bot
        (lookup (gmap_lookup Aux.eq_eqdec Aux.id_aux_countable) name m)
    | _ -> V_bot

  (** val complete : t binding -> t **)

  let complete _ =
    V_bot
 end
