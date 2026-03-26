open Datatypes
open PosDef

module N =
 struct
  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p ->
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double n =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      n

  (** val succ_pos : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_pos n =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> Pos.succ p)
      n

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n' ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun m' ->
        match Pos.sub_mask n' m' with
        | Pos.IsPos p -> p
        | _ -> Big_int_Z.zero_big_int)
        m)
      n

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> Eq)
        (fun _ -> Lt)
        m)
      (fun n' ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> Gt)
        (fun m' -> Pos.compare n' m')
        m)
      n

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.unit_big_int))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun _ -> (Big_int_Z.zero_big_int,
          Big_int_Z.unit_big_int))
          (fun _ -> (Big_int_Z.zero_big_int,
          Big_int_Z.unit_big_int))
          (fun _ -> (Big_int_Z.unit_big_int, Big_int_Z.zero_big_int))
          p)
        b)
      a

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

  (** val coq_lxor :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lxor n m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun q -> Pos.coq_lxor p q)
        m)
      n
 end
