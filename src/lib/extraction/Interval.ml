open BinInt
open Datatypes
open OptionUtil
open Specif
open ZArith_dec

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

  (** val _UU03b1_ : Big_int_Z.big_int -> interval **)

  let _UU03b1_ n =
    Ends (Coq_exist ((Some n), (Some n)))
 end
