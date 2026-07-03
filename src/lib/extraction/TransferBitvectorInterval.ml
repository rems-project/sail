open AbsBitvector
open BinInt
open BinNat
open Bit
open Datatypes
open Interval
open List0
open ListDef
open Nat0
open PeanoNat
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
open List_basics
open Numbers

module B = AbsBitvector.Dom

module I = Dom

module Ops =
 struct
  (** val nonneg_top : I.t **)

  let nonneg_top =
    I.Ends (Coq_exist ((Some Big_int_Z.zero_big_int), None))

  (** val unsigned_lo :
      Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec unsigned_lo bits pow0 =
    match bits with
    | [] -> Big_int_Z.zero_big_int
    | u :: rest ->
      (match u with
       | Three.B1 ->
         Z.add pow0
           (unsigned_lo rest
             (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
               pow0))
       | _ ->
         unsigned_lo rest
           (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) pow0))

  (** val unsigned_hi :
      Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec unsigned_hi bits pow0 =
    match bits with
    | [] -> Big_int_Z.zero_big_int
    | u :: rest ->
      (match u with
       | Three.B0 ->
         unsigned_hi rest
           (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) pow0)
       | _ ->
         Z.add pow0
           (unsigned_hi rest
             (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
               pow0)))

  (** val bits_unsigned_interval : Three.ubit list -> I.t **)

  let bits_unsigned_interval bits =
    I.join (I.abst (unsigned_lo bits Big_int_Z.unit_big_int))
      (I.abst (unsigned_hi bits Big_int_Z.unit_big_int))

  (** val unsigned : B.t -> I.t **)

  let unsigned = function
  | B.Top -> nonneg_top
  | B.Bvs m ->
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun _ bits acc ->
      I.join (bits_unsigned_interval bits) acc) I.bot
      (let Coq_exist a = m in a)

  (** val bits_signed_interval : Three.ubit list -> I.t **)

  let bits_signed_interval bits =
    match rev bits with
    | [] -> I.abst Big_int_Z.zero_big_int
    | sign :: lower_rev ->
      let lower = rev lower_rev in
      let lo = unsigned_lo lower Big_int_Z.unit_big_int in
      let hi = unsigned_hi lower Big_int_Z.unit_big_int in
      let half =
        Z.pow (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
          (Z.of_nat (length lower))
      in
      (match sign with
       | Three.B0 -> I.join (I.abst lo) (I.abst hi)
       | Three.B1 -> I.join (I.abst (Z.sub lo half)) (I.abst (Z.sub hi half))
       | Three.BU -> I.join (I.abst (Z.sub lo half)) (I.abst hi))

  (** val signed : B.t -> I.t **)

  let signed = function
  | B.Top -> I.top
  | B.Bvs m ->
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun _ bits acc ->
      I.join (bits_signed_interval bits) acc) I.bot (let Coq_exist a = m in a)

  (** val zeros_nat : Big_int_Z.big_int -> B.t **)

  let zeros_nat n =
    B.abst { bvn_n = (BinNat.N.of_nat n); bvn_val =
      (bv_0 (BinNat.N.of_nat n)) }

  (** val ones_nat : Big_int_Z.big_int -> B.t **)

  let ones_nat n =
    B.abst { bvn_n = (BinNat.N.of_nat n); bvn_val =
      (bv_not (BinNat.N.of_nat n) (bv_0 (BinNat.N.of_nat n))) }

  (** val nonneg_range :
      I.t -> (Big_int_Z.big_int * Big_int_Z.big_int option) option **)

  let nonneg_range = function
  | I.Empty -> None
  | I.Ends endpoints0 ->
    let (o, o0) = let Coq_exist a = endpoints0 in a in
    (match o with
     | Some lo ->
       (match o0 with
        | Some hi ->
          if Z.ltb hi Big_int_Z.zero_big_int
          then None
          else Some ((Z.to_nat lo), (Some (Z.to_nat hi)))
        | None -> Some ((Z.to_nat lo), None))
     | None ->
       (match o0 with
        | Some hi ->
          if Z.ltb hi Big_int_Z.zero_big_int
          then None
          else Some (Big_int_Z.zero_big_int, (Some (Z.to_nat hi)))
        | None -> Some (Big_int_Z.zero_big_int, None)))

  (** val zeros : Big_int_Z.big_int -> I.t -> B.t **)

  let zeros h n =
    match nonneg_range n with
    | Some p ->
      let (lo, o) = p in
      (match o with
       | Some hi ->
         let widths = sub hi lo in
         if PeanoNat.Nat.leb h widths
         then B.top
         else fold_left (fun b w -> B.join b (zeros_nat w))
                (seq lo (sub hi lo)) (zeros_nat hi)
       | None -> B.top)
    | None -> B.bot

  (** val ones : Big_int_Z.big_int -> I.t -> B.t **)

  let ones h n =
    match nonneg_range n with
    | Some p ->
      let (lo, o) = p in
      (match o with
       | Some hi ->
         let widths = sub hi lo in
         if PeanoNat.Nat.leb h widths
         then B.top
         else fold_left (fun b w -> B.join b (ones_nat w))
                (seq lo (sub hi lo)) (ones_nat hi)
       | None -> B.top)
    | None -> B.bot

  (** val count_leading_B0 : Three.ubit list -> Big_int_Z.big_int **)

  let rec count_leading_B0 = function
  | [] -> Big_int_Z.zero_big_int
  | u :: rest ->
    (match u with
     | Three.B0 ->
       add (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
         (count_leading_B0 rest)
     | _ -> Big_int_Z.zero_big_int)

  (** val count_until_B1 : Three.ubit list -> Big_int_Z.big_int **)

  let rec count_until_B1 = function
  | [] -> Big_int_Z.zero_big_int
  | u :: rest ->
    (match u with
     | Three.B1 -> Big_int_Z.zero_big_int
     | _ ->
       add (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
         (count_until_B1 rest))

  (** val bits_clz_interval : Three.ubit list -> I.t **)

  let bits_clz_interval bits =
    let rev_bits = rev bits in
    let lo = Z.of_nat (count_leading_B0 rev_bits) in
    let hi = Z.of_nat (count_until_B1 rev_bits) in
    I.join (I.abst lo) (I.abst hi)

  (** val count_leading_zeros : B.t -> I.t **)

  let count_leading_zeros = function
  | B.Top -> nonneg_top
  | B.Bvs m ->
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun _ bits acc ->
      I.join (bits_clz_interval bits) acc) I.bot (let Coq_exist a = m in a)

  (** val bits_ctz_interval : Three.ubit list -> I.t **)

  let bits_ctz_interval bits =
    let lo = Z.of_nat (count_leading_B0 bits) in
    let hi = Z.of_nat (count_until_B1 bits) in I.join (I.abst lo) (I.abst hi)

  (** val count_trailing_zeros : B.t -> I.t **)

  let count_trailing_zeros = function
  | B.Top -> nonneg_top
  | B.Bvs m ->
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun _ bits acc ->
      I.join (bits_ctz_interval bits) acc) I.bot (let Coq_exist a = m in a)

  (** val zero_extend_one_width :
      Three.ubit list -> Big_int_Z.big_int -> B.t **)

  let zero_extend_one_width src_bits dst_w =
    let src_w = length src_bits in
    if decide (decide_rel Nat.le_dec src_w dst_w)
    then B.Bvs (Coq_exist
           (singletonM
             (map_singleton (gmap_partial_alter Nat.eq_dec nat_countable)
               (gmap_empty Nat.eq_dec nat_countable))
             dst_w
             (app src_bits (Coq_list.replicate (sub dst_w src_w) Three.B0))))
    else B.bot

  (** val zero_extend_to_width : B.t -> Big_int_Z.big_int -> B.t **)

  let zero_extend_to_width b dst_w =
    match b with
    | B.Top -> B.top
    | B.Bvs m ->
      map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable)
        (fun _ bits acc -> B.join (zero_extend_one_width bits dst_w) acc)
        B.bot (let Coq_exist a = m in a)

  (** val zero_extend : Big_int_Z.big_int -> B.t -> I.t -> B.t **)

  let zero_extend h b n =
    match nonneg_range n with
    | Some p ->
      let (lo, o) = p in
      (match o with
       | Some hi ->
         let widths = sub hi lo in
         if PeanoNat.Nat.leb h widths
         then B.top
         else fold_left (fun acc w -> B.join acc (zero_extend_to_width b w))
                (seq lo (sub hi lo)) (zero_extend_to_width b hi)
       | None -> B.top)
    | None -> B.bot

  (** val sign_extend_one_width :
      Three.ubit list -> Big_int_Z.big_int -> B.t **)

  let sign_extend_one_width src_bits dst_w =
    let src_w = length src_bits in
    if decide (decide_rel Nat.le_dec src_w dst_w)
    then let sign = match rev src_bits with
                    | [] -> Three.B0
                    | s :: _ -> s in
         B.Bvs (Coq_exist
         (singletonM
           (map_singleton (gmap_partial_alter Nat.eq_dec nat_countable)
             (gmap_empty Nat.eq_dec nat_countable))
           dst_w (app src_bits (Coq_list.replicate (sub dst_w src_w) sign))))
    else B.bot

  (** val sign_extend_to_width : B.t -> Big_int_Z.big_int -> B.t **)

  let sign_extend_to_width b dst_w =
    match b with
    | B.Top -> B.top
    | B.Bvs m ->
      map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable)
        (fun _ bits acc -> B.join (sign_extend_one_width bits dst_w) acc)
        B.bot (let Coq_exist a = m in a)

  (** val sign_extend : Big_int_Z.big_int -> B.t -> I.t -> B.t **)

  let sign_extend h b n =
    match nonneg_range n with
    | Some p ->
      let (lo, o) = p in
      (match o with
       | Some hi ->
         let widths = sub hi lo in
         if PeanoNat.Nat.leb h widths
         then B.top
         else fold_left (fun acc w -> B.join acc (sign_extend_to_width b w))
                (seq lo (sub hi lo)) (sign_extend_to_width b hi)
       | None -> B.top)
    | None -> B.bot

  (** val bits_length : B.t -> I.t **)

  let bits_length = function
  | B.Top -> nonneg_top
  | B.Bvs m ->
    map_fold (fun _ -> gmap_fold Nat.eq_dec nat_countable) (fun w _ acc ->
      I.join (I.abst (Z.of_nat w)) acc) I.bot (let Coq_exist a = m in a)
 end
