open BinInt
open Datatypes
open OptionUtil
open Specif
open ZArith_dec
open Base
open Option

module Dom =
 struct
  type endpoints =
    (Big_int_Z.big_int option * Big_int_Z.big_int option) coq_sig

  type interval =
  | Empty
  | Ends of endpoints

  (** val interval_rect : 'a1 -> (endpoints -> 'a1) -> interval -> 'a1 **)

  let interval_rect f f0 = function
  | Empty -> f
  | Ends e -> f0 e

  (** val interval_rec : 'a1 -> (endpoints -> 'a1) -> interval -> 'a1 **)

  let interval_rec f f0 = function
  | Empty -> f
  | Ends e -> f0 e

  type t = interval

  (** val low : endpoints -> Big_int_Z.big_int option **)

  let low i =
    fst (let Coq_exist a = i in a)

  (** val high : endpoints -> Big_int_Z.big_int option **)

  let high i =
    snd (let Coq_exist a = i in a)

  (** val extend :
      (Big_int_Z.big_int -> Big_int_Z.big_int -> bool) -> Big_int_Z.big_int
      option -> Big_int_Z.big_int option -> Big_int_Z.big_int option **)

  let extend op end_UU2080_ end_UU2081_ =
    match end_UU2080_ with
    | Some e_UU2080_ ->
      (match end_UU2081_ with
       | Some e_UU2081_ ->
         if op e_UU2080_ e_UU2081_ then end_UU2080_ else end_UU2081_
       | None -> None)
    | None -> None

  (** val join : interval -> interval -> interval **)

  let join i_UU2080_ i_UU2081_ =
    match i_UU2080_ with
    | Empty -> i_UU2081_
    | Ends i_UU2080_0 ->
      (match i_UU2081_ with
       | Empty -> Ends i_UU2080_0
       | Ends i_UU2081_0 ->
         Ends (Coq_exist ((extend Z.ltb (low i_UU2080_0) (low i_UU2081_0)),
           (extend Z.gtb (high i_UU2080_0) (high i_UU2081_0)))))

  (** val meet : interval -> interval -> interval **)

  let meet i_UU2080_ i_UU2081_ =
    match i_UU2080_ with
    | Empty -> Empty
    | Ends i_UU2080_0 ->
      (match i_UU2081_ with
       | Empty -> Empty
       | Ends i_UU2081_0 ->
         let l = option_join Z.max (low i_UU2080_0) (low i_UU2081_0) in
         let h = option_join Z.min (high i_UU2080_0) (high i_UU2081_0) in
         (match l with
          | Some l0 ->
            (match h with
             | Some h0 ->
               if coq_Z_le_dec l0 h0
               then Ends (Coq_exist ((Some l0), (Some h0)))
               else Empty
             | None -> Ends (Coq_exist ((Some l0), None)))
          | None ->
            (match h with
             | Some h0 -> Ends (Coq_exist (None, (Some h0)))
             | None -> Ends (Coq_exist (None, None)))))

  (** val bot : interval **)

  let bot =
    Empty

  (** val top : interval **)

  let top =
    Ends (Coq_exist (None, None))

  (** val low_leb :
      Big_int_Z.big_int option -> Big_int_Z.big_int option -> bool **)

  let low_leb x y =
    match x with
    | Some x0 -> (match y with
                  | Some y0 -> Z.leb x0 y0
                  | None -> false)
    | None -> true

  (** val high_leb :
      Big_int_Z.big_int option -> Big_int_Z.big_int option -> bool **)

  let high_leb x y =
    match x with
    | Some x0 -> (match y with
                  | Some y0 -> Z.leb x0 y0
                  | None -> true)
    | None -> (match y with
               | Some _ -> false
               | None -> true)

  (** val leb : interval -> interval -> bool **)

  let leb i_UU2080_ i_UU2081_ =
    match i_UU2080_ with
    | Empty -> true
    | Ends e_UU2080_ ->
      (match i_UU2081_ with
       | Empty -> false
       | Ends e_UU2081_ ->
         (&&) (low_leb (low e_UU2081_) (low e_UU2080_))
           (high_leb (high e_UU2080_) (high e_UU2081_)))

  (** val abst : Big_int_Z.big_int -> interval **)

  let abst n =
    Ends (Coq_exist ((Some n), (Some n)))

  (** val concrete : interval -> Big_int_Z.big_int option **)

  let concrete = function
  | Empty -> None
  | Ends ep ->
    let (o, o0) = let Coq_exist a = ep in a in
    (match o with
     | Some lo ->
       (match o0 with
        | Some hi -> if Z.eqb lo hi then Some lo else None
        | None -> None)
     | None -> None)

  (** val compare_endpoints :
      (Big_int_Z.big_int -> Big_int_Z.big_int -> bool) -> Big_int_Z.big_int
      option -> Big_int_Z.big_int option -> bool **)

  let compare_endpoints op x y =
    match x with
    | Some a -> (match y with
                 | Some b -> op a b
                 | None -> false)
    | None -> false

  (** val lt : interval -> interval -> bool option **)

  let lt x y =
    match x with
    | Empty -> None
    | Ends ex ->
      (match y with
       | Empty -> None
       | Ends ey ->
         if compare_endpoints Z.ltb (high ex) (low ey)
         then Some true
         else if compare_endpoints Z.leb (high ey) (low ex)
              then Some false
              else None)

  (** val gt : interval -> interval -> bool option **)

  let gt x y =
    match x with
    | Empty -> None
    | Ends ex ->
      (match y with
       | Empty -> None
       | Ends ey ->
         if compare_endpoints Z.ltb (high ey) (low ex)
         then Some true
         else if compare_endpoints Z.leb (high ex) (low ey)
              then Some false
              else None)

  (** val lteq : interval -> interval -> bool option **)

  let lteq x y =
    match x with
    | Empty -> None
    | Ends ex ->
      (match y with
       | Empty -> None
       | Ends ey ->
         if compare_endpoints Z.leb (high ex) (low ey)
         then Some true
         else if compare_endpoints Z.ltb (high ey) (low ex)
              then Some false
              else None)

  (** val gteq : interval -> interval -> bool option **)

  let gteq x y =
    match x with
    | Empty -> None
    | Ends ex ->
      (match y with
       | Empty -> None
       | Ends ey ->
         if compare_endpoints Z.leb (high ey) (low ex)
         then Some true
         else if compare_endpoints Z.ltb (high ex) (low ey)
              then Some false
              else None)

  (** val negate_endpoints :
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let negate_endpoints x =
    ((fmap (Obj.magic (fun _ _ -> option_fmap)) Z.opp (snd x)),
      (fmap (Obj.magic (fun _ _ -> option_fmap)) Z.opp (fst x)))

  (** val negate : interval -> interval **)

  let negate = function
  | Empty -> Empty
  | Ends e -> Ends (Coq_exist (negate_endpoints (let Coq_exist a = e in a)))

  (** val add_endpoints :
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let add_endpoints x y =
    let l = option_map2 Z.add (fst x) (fst y) in
    let h = option_map2 Z.add (snd x) (snd y) in (l, h)

  (** val add : interval -> interval -> interval **)

  let add x y =
    match x with
    | Empty -> Empty
    | Ends e1 ->
      (match y with
       | Empty -> Empty
       | Ends e2 ->
         Ends (Coq_exist
           (add_endpoints (let Coq_exist a = e1 in a)
             (let Coq_exist a = e2 in a))))

  (** val sub : interval -> interval -> interval **)

  let sub x y =
    add x (negate y)

  (** val four_corner_endpoints :
      (Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int) ->
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let four_corner_endpoints op x y =
    let p = (((fst x), (snd x)), (fst y)) in
    let o = snd y in
    let (p0, o0) = p in
    let (o1, o2) = p0 in
    (match o1 with
     | Some lx ->
       (match o2 with
        | Some hx ->
          (match o0 with
           | Some ly ->
             (match o with
              | Some hy ->
                let v1 = op lx ly in
                let v2 = op lx hy in
                let v3 = op hx ly in
                let v4 = op hx hy in
                ((Some (Z.min v1 (Z.min v2 (Z.min v3 v4)))), (Some
                (Z.max v1 (Z.max v2 (Z.max v3 v4)))))
              | None -> (None, None))
           | None -> (None, None))
        | None -> (None, None))
     | None -> (None, None))

  (** val lift_binop :
      (Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int) ->
      interval -> interval -> interval **)

  let lift_binop op x y =
    match x with
    | Empty -> Empty
    | Ends e1 ->
      (match y with
       | Empty -> Empty
       | Ends e2 ->
         Ends (Coq_exist
           (four_corner_endpoints op (let Coq_exist a = e1 in a)
             (let Coq_exist a = e2 in a))))

  (** val mult : interval -> interval -> interval **)

  let mult x y =
    lift_binop Z.mul x y

  (** val max_endpoints :
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let max_endpoints x y =
    ((option_join Z.max (fst x) (fst y)), (option_map2 Z.max (snd x) (snd y)))

  (** val max : interval -> interval -> interval **)

  let max x y =
    match x with
    | Empty -> Empty
    | Ends e1 ->
      (match y with
       | Empty -> Empty
       | Ends e2 ->
         Ends (Coq_exist
           (max_endpoints (let Coq_exist a = e1 in a)
             (let Coq_exist a = e2 in a))))

  (** val min_endpoints :
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let min_endpoints x y =
    ((option_map2 Z.min (fst x) (fst y)), (option_join Z.min (snd x) (snd y)))

  (** val min : interval -> interval -> interval **)

  let min x y =
    match x with
    | Empty -> Empty
    | Ends e1 ->
      (match y with
       | Empty -> Empty
       | Ends e2 ->
         Ends (Coq_exist
           (min_endpoints (let Coq_exist a = e1 in a)
             (let Coq_exist a = e2 in a))))

  (** val abs_endpoint :
      (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
      Big_int_Z.big_int option * Big_int_Z.big_int option **)

  let abs_endpoint x =
    let o = fst x in
    let o0 = snd x in
    (match o with
     | Some l ->
       (match o0 with
        | Some h ->
          if Z.leb Big_int_Z.zero_big_int l
          then ((Some l), (Some h))
          else if Z.ltb h Big_int_Z.zero_big_int
               then ((Some (Z.opp h)), (Some (Z.opp l)))
               else ((Some Big_int_Z.zero_big_int), (Some
                      (Z.max (Z.opp l) h)))
        | None ->
          if Z.leb Big_int_Z.zero_big_int l
          then ((Some l), None)
          else ((Some Big_int_Z.zero_big_int), None))
     | None ->
       (match o0 with
        | Some h ->
          if Z.ltb h Big_int_Z.zero_big_int
          then ((Some (Z.opp h)), None)
          else ((Some Big_int_Z.zero_big_int), None)
        | None -> ((Some Big_int_Z.zero_big_int), None)))

  (** val abs : interval -> interval **)

  let abs = function
  | Empty -> Empty
  | Ends e -> Ends (Coq_exist (abs_endpoint (let Coq_exist a = e in a)))

  (** val tdiv : interval -> interval -> interval **)

  let tdiv x y =
    lift_binop Z.quot x y

  (** val tmod : interval -> interval -> interval **)

  let tmod x y =
    lift_binop Z.rem x y

  (** val fdiv : interval -> interval -> interval **)

  let fdiv x y =
    lift_binop Z.div x y

  (** val fmod : interval -> interval -> interval **)

  let fmod x y =
    lift_binop Z.modulo x y

  (** val ediv : interval -> interval -> interval **)

  let ediv x y =
    lift_binop (fun a b -> fst (Z.div_eucl a b)) x y

  (** val emod : interval -> interval -> interval **)

  let emod x y =
    lift_binop (fun a b -> snd (Z.div_eucl a b)) x y
 end
