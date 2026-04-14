open BinNat
open Bit
open List0
open ListDef
open OptionUtil
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
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

  (** val _UU03b1_ : bvn -> t **)

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
 end
