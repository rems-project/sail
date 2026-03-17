open Ast
open BinInt
open Bit
open BitList
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open Nat0
open PeanoNat
open QArith_base
open TypeAnnot

type 'v binding =
| Complete of value
| Partial of (('v * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty

(** val combine_binding :
    'a1 binding option -> 'a1 binding option -> 'a1 binding option **)

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
    'a1 binding IdMap.t -> 'a1 binding IdMap.t -> 'a1 binding IdMap.t **)

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

(** val complete_bindings : value binding IdMap.t -> value IdMap.t **)

let complete_bindings m =
  IdMap.map (fun b ->
    match b with
    | Complete v -> v
    | Partial vs -> complete_value vs) m

type 'v match_result =
| Matched of 'v binding IdMap.t
| MaybeMatched of 'v binding IdMap.t
| Unmatched

(** val merge_match_result :
    value match_result -> value match_result -> value match_result **)

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

(** val empty_bindings : value binding IdMap.t **)

let empty_bindings =
  IdMap.empty

(** val simple_match : value match_result **)

let simple_match =
  Matched empty_bindings

(** val simple_match_when : bool -> value match_result **)

let simple_match_when = function
| true -> simple_match
| false -> Unmatched

(** val add_match :
    id -> value binding -> value match_result -> value match_result **)

let add_match k v = function
| Matched b -> Matched (IdMap.add k v b)
| MaybeMatched b -> MaybeMatched (IdMap.add k v b)
| Unmatched -> Unmatched

(** val neg_match : value match_result -> value match_result **)

let neg_match = function
| Matched _ -> Unmatched
| MaybeMatched b -> MaybeMatched b
| Unmatched -> simple_match

(** val or_match :
    value match_result -> value match_result -> value match_result **)

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
      | V_int m -> simple_match_when (Z.eqb n m)
      | _ -> Unmatched)
   | L_hex s ->
     (match v with
      | V_bitvector vs -> simple_match_when (same_bits (of_hex_lit s) vs)
      | _ -> Unmatched)
   | L_bin s ->
     (match v with
      | V_bitvector vs -> simple_match_when (same_bits (of_bin_lit s) vs)
      | _ -> Unmatched)
   | L_string s1 ->
     (match v with
      | V_string s2 -> simple_match_when ((=) s1 s2)
      | _ -> Unmatched)
   | L_real r1 ->
     (match v with
      | V_real r2 -> simple_match_when (coq_Qeq_bool r1 r2)
      | _ -> Unmatched))

(** val get_struct_field : id -> (id * value) list -> value **)

let rec get_struct_field name = function
| [] -> V_unit
| p :: rest_fields ->
  let (name', v) = p in
  if id_eqb name name' then v else get_struct_field name rest_fields

module Make =
 functor (Tannot:S) ->
 struct
  (** val fold_match :
      (Tannot.t pat -> value -> value match_result) -> Tannot.t pat list ->
      (value match_result * value list) -> value match_result * value list **)

  let rec fold_match f ps match_info =
    match ps with
    | [] -> match_info
    | p :: ps0 ->
      let match_info0 =
        let (prev, l) = match_info in
        (match l with
         | [] -> (Unmatched, [])
         | v :: vs -> ((merge_match_result prev (f p v)), vs))
      in
      fold_match f ps0 match_info0

  (** val pattern_match : Tannot.t pat -> value -> value match_result **)

  let rec pattern_match p v =
    let P_aux (aux, annot) = p in
    (match aux with
     | P_lit l -> pattern_match_literal l v
     | P_or (lhs_p, rhs_p) ->
       or_match (pattern_match lhs_p v) (pattern_match rhs_p v)
     | P_not p0 -> neg_match (pattern_match p0 v)
     | P_as (p0, n) -> add_match n (Complete v) (pattern_match p0 v)
     | P_typ (_, p0) -> pattern_match p0 v
     | P_id n ->
       (match Tannot.get_id_type (snd annot) n with
        | Enum_member ->
          (match v with
           | V_member m -> simple_match_when (id_eqb n m)
           | _ -> Unmatched)
        | _ -> Matched (IdMap.add n (Complete v) empty_bindings))
     | P_var (p0, _) -> pattern_match p0 v
     | P_app (ctor, ps) ->
       (match v with
        | V_ctor (v_ctor, vs) ->
          if id_eqb ctor v_ctor
          then fst (fold_match pattern_match ps (simple_match, vs))
          else Unmatched
        | _ -> Unmatched)
     | P_vector ps ->
       (match to_gvector v with
        | V_vector vs -> fst (fold_match pattern_match ps (simple_match, vs))
        | _ -> Unmatched)
     | P_vector_concat ps ->
       (match v with
        | V_bitvector bs ->
          fst
            (fold_left (fun match_info p0 ->
              let P_aux (_, annot0) = p0 in
              (match Tannot.get_split (snd annot0) with
               | No_split -> (Unmatched, [])
               | Split s ->
                 let (prev, bs0) = match_info in
                 (match bs0 with
                  | [] -> (Unmatched, [])
                  | _ :: _ ->
                    let (bs_take, bs_drop) = take_drop s bs0 in
                    ((merge_match_result prev
                       (pattern_match p0 (V_bitvector bs_take))),
                    bs_drop))))
              ps (simple_match, bs))
        | V_vector vs ->
          fst
            (fold_left (fun match_info p0 ->
              let P_aux (_, annot0) = p0 in
              (match Tannot.get_split (snd annot0) with
               | No_split -> (Unmatched, [])
               | Split s ->
                 let (prev, vs0) = match_info in
                 (match vs0 with
                  | [] -> (Unmatched, [])
                  | _ :: _ ->
                    let (vs_take, vs_drop) = take_drop s vs0 in
                    ((merge_match_result prev
                       (pattern_match p0 (V_vector vs_take))),
                    vs_drop))))
              ps (simple_match, vs))
        | _ -> Unmatched)
     | P_vector_subrange (id0, n, m) ->
       Matched
         (IdMap.add id0 (Partial (Non_empty (((v, n), m), [])))
           empty_bindings)
     | P_tuple ps ->
       (match ps with
        | [] -> (match v with
                 | V_unit -> simple_match
                 | _ -> Unmatched)
        | _ :: _ ->
          (match v with
           | V_tuple vs ->
             fst (fold_match pattern_match ps (simple_match, vs))
           | _ -> Unmatched))
     | P_list ps ->
       (match v with
        | V_list vs ->
          if Nat.eqb (length ps) (length vs)
          then fst (fold_match pattern_match ps (simple_match, vs))
          else Unmatched
        | _ -> Unmatched)
     | P_cons (p0, ps) ->
       (match v with
        | V_list l ->
          (match l with
           | [] -> Unmatched
           | v0 :: vs ->
             merge_match_result (pattern_match p0 v0)
               (pattern_match ps (V_list vs)))
        | _ -> Unmatched)
     | P_struct (_, field_patterns, _) ->
       (match v with
        | V_record fields ->
          fold_left (fun prev fp ->
            let (name, p0) = fp in
            let v0 = get_struct_field name fields in
            merge_match_result prev (pattern_match p0 v0)) field_patterns
            simple_match
        | _ -> Unmatched)
     | _ -> simple_match)
 end
