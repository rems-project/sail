open Ast
open BinInt
open Bit
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open Nat0

type binding =
| Complete of value
| Partial of ((value * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty

(** val combine_binding :
    binding option -> binding option -> binding option **)

let combine_binding l r =
  match l with
  | Some lb ->
    (match r with
     | Some rb ->
       (match lb with
        | Complete v -> Some (Complete v)
        | Partial n ->
          let Non_empty (lv, lvs) = n in
          (match rb with
           | Complete v -> Some (Complete v)
           | Partial n0 ->
             let Non_empty (rv, rvs) = n0 in
             Some (Partial (Non_empty (lv, (app lvs (rv :: rvs)))))))
     | None -> Some lb)
  | None -> r

(** val merge_bindings :
    binding IdMap.t -> binding IdMap.t -> binding IdMap.t **)

let merge_bindings l r =
  IdMap.map2 combine_binding l r

(** val update_list : bit list -> Big_int_Z.big_int -> bit -> bit list **)

let update_list xs n y =
  let n0 =
    sub (sub (length xs) n) (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
  in
  let (ys, zs) = take_drop n0 xs in app ys (app (y :: []) (tl zs))

(** val update_subrange :
    bit list -> Big_int_Z.big_int -> bit list -> bit list **)

let rec update_subrange xs n = function
| [] -> xs
| y :: ys0 ->
  update_subrange (update_list xs n y)
    (sub n (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) ys0

(** val complete_value :
    ((value * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> value **)

let complete_value = function
| Non_empty (p, partial_values0) ->
  let (p0, m1) = p in
  let (v1, n1) = p0 in
  let (max0, min0) =
    fold_left (fun range pvalue ->
      let (max0, min0) = range in
      let (y, m) = pvalue in
      let (_, n) = y in ((Z.max max0 (Z.max n m)), (Z.min min0 (Z.min n m))))
      partial_values0 (n1, m1)
  in
  let len = Z.sub (Z.succ max0) min0 in
  let zeros = repeat B0 (Z.to_nat len) in
  let value0 =
    fold_left (fun bv pvalue ->
      let (y, _) = pvalue in
      let (slice, n) = y in
      (match slice with
       | V_bitvector slice0 -> update_subrange bv (Z.to_nat n) slice0
       | _ -> bv))
      (((v1, n1), m1) :: partial_values0) zeros
  in
  V_bitvector value0

(** val complete_bindings : binding IdMap.t -> value IdMap.t **)

let complete_bindings m =
  IdMap.map (fun b ->
    match b with
    | Complete v -> v
    | Partial vs -> complete_value vs) m

type match_result =
| Matched of binding IdMap.t
| MaybeMatched of binding IdMap.t
| Unmatched

(** val merge_match_result : match_result -> match_result -> match_result **)

let merge_match_result l r =
  match l with
  | Matched l_b ->
    (match r with
     | Matched r_b -> Matched (merge_bindings l_b r_b)
     | MaybeMatched r_b -> MaybeMatched (merge_bindings l_b r_b)
     | Unmatched -> Unmatched)
  | MaybeMatched l_b ->
    (match r with
     | Matched r_b -> MaybeMatched (merge_bindings l_b r_b)
     | MaybeMatched r_b -> MaybeMatched (merge_bindings l_b r_b)
     | Unmatched -> Unmatched)
  | Unmatched -> Unmatched

(** val empty_bindings : binding IdMap.t **)

let empty_bindings =
  IdMap.empty

(** val simple_match : match_result **)

let simple_match =
  Matched empty_bindings

(** val simple_match_when : bool -> match_result **)

let simple_match_when = function
| true -> simple_match
| false -> Unmatched

(** val add_match : id -> binding -> match_result -> match_result **)

let add_match k v = function
| Matched b -> Matched (IdMap.add k v b)
| MaybeMatched b -> MaybeMatched (IdMap.add k v b)
| Unmatched -> Unmatched

(** val neg_match : match_result -> match_result **)

let neg_match = function
| Matched _ -> Unmatched
| MaybeMatched b -> MaybeMatched b
| Unmatched -> simple_match

(** val or_match : match_result -> match_result -> match_result **)

let or_match l r =
  match l with
  | Matched l_b -> Matched l_b
  | MaybeMatched l_b ->
    (match r with
     | Matched r_b -> Matched r_b
     | _ -> MaybeMatched l_b)
  | Unmatched -> r

(** val binds_id : id -> 'a1 pat -> bool **)

let rec binds_id n = function
| P_aux (aux, _) ->
  (match aux with
   | P_or (p1, p2) -> (||) (binds_id n p1) (binds_id n p2)
   | P_as (pat0, m) -> (||) (binds_id n pat0) (id_eqb n m)
   | P_typ (_, p0) -> binds_id n p0
   | P_id m -> id_eqb n m
   | P_var (p0, _) -> binds_id n p0
   | P_app (_, ps) -> fold_left (||) (map (binds_id n) ps) false
   | P_vector ps -> fold_left (||) (map (binds_id n) ps) false
   | P_vector_concat ps -> fold_left (||) (map (binds_id n) ps) false
   | P_vector_subrange (m, _, _) -> id_eqb n m
   | P_tuple ps -> fold_left (||) (map (binds_id n) ps) false
   | P_list ps -> fold_left (||) (map (binds_id n) ps) false
   | P_cons (p1, p2) -> (||) (binds_id n p1) (binds_id n p2)
   | P_string_append ps -> fold_left (||) (map (binds_id n) ps) false
   | P_struct (_, ps, _) ->
     fold_left (||) (map (fun fp -> binds_id n (snd fp)) ps) false
   | _ -> false)
