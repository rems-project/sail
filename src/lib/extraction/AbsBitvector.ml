open BinNat
open Bit
open Datatypes
open List0
open ListDef
open Nat0
open OptionUtil
open PeanoNat
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
open List_basics
open Numbers

module Bits =
 struct
  type t = bvn
 end

module Dom =
 struct
  type bvset =
  | Top
  | Bvs of (Big_int_Z.big_int, Three.ubit list) gmap coq_sig

  (** val bvset_rect :
      'a1 -> ((Big_int_Z.big_int, Three.ubit list) gmap coq_sig -> 'a1) ->
      bvset -> 'a1 **)

  let bvset_rect f f0 = function
  | Top -> f
  | Bvs s -> f0 s

  (** val bvset_rec :
      'a1 -> ((Big_int_Z.big_int, Three.ubit list) gmap coq_sig -> 'a1) ->
      bvset -> 'a1 **)

  let bvset_rec f f0 = function
  | Top -> f
  | Bvs s -> f0 s

  (** val to_bv_list : bvset -> Three.ubit list list option **)

  let to_bv_list = function
  | Top -> None
  | Bvs x0 ->
    Some
      (map snd
        (map_to_list (fun _ -> gmap_fold Nat.eq_dec nat_countable)
          (let Coq_exist a = x0 in a)))

  type t = bvset

  (** val top : bvset **)

  let top =
    Top

  (** val bot : t **)

  let bot =
    Bvs (Coq_exist (empty (gmap_empty Nat.eq_dec nat_countable)))

  (** val join_aux :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap **)

  let join_aux x y =
    merge (Obj.magic (fun _ _ _ -> gmap_merge Nat.eq_dec nat_countable))
      (option_join (zip_with Three.bit_join)) x y

  (** val join : t -> t -> t **)

  let join x y =
    match x with
    | Top -> Top
    | Bvs x0 ->
      (match y with
       | Top -> Top
       | Bvs y0 ->
         Bvs (Coq_exist
           (join_aux (let Coq_exist a = x0 in a) (let Coq_exist a = y0 in a))))

  (** val meet_aux :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap **)

  let meet_aux x y =
    merge (Obj.magic (fun _ _ _ -> gmap_merge Nat.eq_dec nat_countable))
      (option_bind2 (fun xs ys -> option_all (zip_with Three.bit_meet xs ys)))
      x y

  (** val meet : t -> t -> t **)

  let meet x y =
    match x with
    | Top -> y
    | Bvs x0 ->
      (match y with
       | Top -> x
       | Bvs y0 ->
         Bvs (Coq_exist
           (meet_aux (let Coq_exist a = x0 in a) (let Coq_exist a = y0 in a))))

  (** val leb_aux :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> bool **)

  let leb_aux x y =
    forallb (fun pat ->
      let (k, xv) = pat in
      (match lookup (gmap_lookup Nat.eq_dec nat_countable) k y with
       | Some yv ->
         forallb (fun pat0 -> let (xb, yb) = pat0 in Three.bit_leb xb yb)
           (zip_with (fun x0 x1 -> (x0, x1)) xv yv)
       | None -> false))
      (map_to_list (fun _ -> gmap_fold Nat.eq_dec nat_countable) x)

  (** val leb : t -> t -> bool **)

  let leb x y =
    match x with
    | Top -> (match y with
              | Top -> true
              | Bvs _ -> false)
    | Bvs x0 ->
      (match y with
       | Top -> true
       | Bvs y0 ->
         leb_aux (let Coq_exist a = x0 in a) (let Coq_exist a = y0 in a))

  (** val _UU03b1_ : bvn -> bvset **)

  let _UU03b1_ x =
    let len = x.bvn_n in
    (match bvn_to_bv len x with
     | Some x' ->
       Bvs (Coq_exist
         (singletonM
           (map_singleton (gmap_partial_alter Nat.eq_dec nat_countable)
             (gmap_empty Nat.eq_dec nat_countable))
           (BinNat.N.to_nat len) (map Three.from_bool (bv_to_bits len x'))))
     | None -> bot)

  (** val lift_bitwise_gmap :
      (Three.ubit -> Three.ubit -> Three.ubit) -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap ->
      (Big_int_Z.big_int, Three.ubit list) gmap **)

  let lift_bitwise_gmap f x y =
    intersection_with
      (map_intersection_with
        (Obj.magic (fun _ _ _ -> gmap_merge Nat.eq_dec nat_countable)))
      (fun x0 y0 -> Some (zip_with f x0 y0)) x y

  (** val lift_bitwise :
      (Three.ubit -> Three.ubit -> Three.ubit) -> bvset -> bvset -> bvset **)

  let lift_bitwise f x y =
    match x with
    | Top -> Top
    | Bvs x0 ->
      (match y with
       | Top -> Top
       | Bvs y0 ->
         Bvs (Coq_exist
           (lift_bitwise_gmap f (let Coq_exist a = x0 in a)
             (let Coq_exist a = y0 in a))))

  (** val coq_and : bvset -> bvset -> bvset **)

  let coq_and x y =
    lift_bitwise Three.bit_and x y

  (** val coq_or : bvset -> bvset -> bvset **)

  let coq_or x y =
    lift_bitwise Three.bit_or x y

  (** val xor : bvset -> bvset -> bvset **)

  let xor x y =
    lift_bitwise Three.bit_xor x y

  (** val not_gmap :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap **)

  let not_gmap x =
    fmap (Obj.magic (fun _ _ -> gmap_fmap Nat.eq_dec nat_countable))
      (map Three.bit_not) x

  (** val not : bvset -> bvset **)

  let not = function
  | Top -> Top
  | Bvs x0 -> Bvs (Coq_exist (not_gmap (let Coq_exist a = x0 in a)))

  (** val add_gmap :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap **)

  let add_gmap x y =
    intersection_with
      (map_intersection_with
        (Obj.magic (fun _ _ _ -> gmap_merge Nat.eq_dec nat_countable)))
      (fun x0 y0 -> Some
      (rev (fst (Three.bitlist_add_carry_acc x0 y0 Three.B0 [])))) x y

  (** val add : bvset -> bvset -> bvset **)

  let add x y =
    match x with
    | Top -> Top
    | Bvs x0 ->
      (match y with
       | Top -> Top
       | Bvs y0 ->
         Bvs (Coq_exist
           (add_gmap (let Coq_exist a = x0 in a) (let Coq_exist a = y0 in a))))

  (** val append_insert :
      Three.ubit list -> Three.ubit list option -> Three.ubit list option **)

  let append_insert bv = function
  | Some bv' -> Some (zip_with Three.bit_join bv bv')
  | None -> Some bv

  (** val append_gmap :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap **)

  let append_gmap x y =
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun n xbv acc ->
      map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable)
        (fun m ybv acc0 ->
        partial_alter (gmap_partial_alter Nat.eq_dec nat_countable)
          (append_insert (app ybv xbv)) (Nat0.add n m) acc0)
        acc y)
      (empty (gmap_empty Nat.eq_dec nat_countable)) x

  (** val append : bvset -> bvset -> bvset **)

  let append x y =
    match x with
    | Top -> Top
    | Bvs x0 ->
      (match y with
       | Top -> Top
       | Bvs y0 ->
         Bvs (Coq_exist
           (append_gmap (let Coq_exist a = x0 in a)
             (let Coq_exist a = y0 in a))))

  (** val one_bits : Big_int_Z.big_int -> Three.ubit list **)

  let one_bits n =
    if PeanoNat.Nat.eqb n Big_int_Z.zero_big_int
    then []
    else Three.B1 :: (Coq_list.replicate
                       (sub n (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))
                       Three.B0)

  (** val negate_gmap :
      (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
      Three.ubit list) gmap **)

  let negate_gmap x =
    add_gmap (not_gmap x)
      (fmap (Obj.magic (fun _ _ -> gmap_fmap Nat.eq_dec nat_countable))
        (fun bits -> one_bits (length bits)) x)

  (** val negate : bvset -> bvset **)

  let negate = function
  | Top -> Top
  | Bvs x0 -> Bvs (Coq_exist (negate_gmap (let Coq_exist a = x0 in a)))

  (** val sub : bvset -> bvset -> bvset **)

  let sub x y =
    add x (negate y)

  (** val slice_bits :
      Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int -> Three.ubit
      list **)

  let slice_bits bits s m =
    firstn m
      (app (skipn s bits)
        (Coq_list.replicate (Nat0.sub m (length (skipn s bits))) Three.B0))

  (** val slice_gmap :
      (Big_int_Z.big_int, Three.ubit list) gmap -> Big_int_Z.big_int ->
      Big_int_Z.big_int -> (Big_int_Z.big_int, Three.ubit list) gmap **)

  let slice_gmap x s m =
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun _ bits acc ->
      partial_alter (gmap_partial_alter Nat.eq_dec nat_countable)
        (append_insert
          (slice_bits bits (BinNat.N.to_nat s) (BinNat.N.to_nat m)))
        (BinNat.N.to_nat m) acc)
      (empty (gmap_empty Nat.eq_dec nat_countable)) x

  (** val slice : bvset -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvset **)

  let slice x s m =
    match x with
    | Top ->
      Bvs (Coq_exist
        (singletonM
          (map_singleton (gmap_partial_alter Nat.eq_dec nat_countable)
            (gmap_empty Nat.eq_dec nat_countable))
          (BinNat.N.to_nat m)
          (Coq_list.replicate (BinNat.N.to_nat m) Three.BU)))
    | Bvs x0 -> Bvs (Coq_exist (slice_gmap (let Coq_exist a = x0 in a) s m))
 end
