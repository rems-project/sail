open BinPos
open Datatypes
open PosDef

module N =
 struct
  (** val succ_pos : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_pos n =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> Pos.succ p)
      n

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = (fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val coq_lor :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lor n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun q -> (Pos.coq_lor p q))
        m)
      n

  (** val coq_land :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_land n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> Big_int_Z.zero_big_int)
        (fun q -> Pos.coq_land p q)
        m)
      n

  (** val ldiff :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let ldiff n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun q -> Pos.ldiff p q)
        m)
      n

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul = Big_int_Z.mult_big_int

  (** val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let testbit a n =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> false)
      (fun p -> BinPos.Pos.testbit p n)
      a

  (** val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_nat a =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_nat n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n' -> (Pos.of_succ_nat n'))
      n

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec = Big_int_Z.eq_big_int
 end
