open Datatypes
open Decimal
open Hexadecimal
open Nat0
open PosDef

module Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ = Big_int_Z.succ_big_int

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add = Big_int_Z.add_big_int

  (** val add_carry :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (succ q))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  (** val pred_N : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> (pred_double p))
      (fun _ -> Big_int_Z.zero_big_int)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big_int_Z.unit_big_int
  | IsPos p ->
    IsPos ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Big_int_Z.mult_int_big_int 2 p)
  | x0 -> x0

  (** val double_pred_mask : Big_int_Z.big_int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> IsPos (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 p)))
      (fun p -> IsPos (Big_int_Z.mult_int_big_int 2
      (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = (fun n m -> Big_int_Z.max_big_int
  Big_int_Z.unit_big_int (Big_int_Z.sub_big_int n m))

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul = Big_int_Z.mult_big_int

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Big_int_Z.big_int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> Big_int_Z.unit_big_int)
      p

  (** val compare_cont :
      comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare_cont = (fun c x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then c else if s < 0 then Lt else Gt)

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val sqrtrem_step :
      (Big_int_Z.big_int -> Big_int_Z.big_int) -> (Big_int_Z.big_int ->
      Big_int_Z.big_int) -> (Big_int_Z.big_int * mask) ->
      Big_int_Z.big_int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' =
         (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
         (Big_int_Z.mult_int_big_int 2 s)
       in
       let r' = g (f r) in
       if leb s' r'
       then (((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              s), (sub_mask r' s'))
       else ((Big_int_Z.mult_int_big_int 2 s), (IsPos r'))
     | _ ->
       ((Big_int_Z.mult_int_big_int 2 s),
         (sub_mask (g (f Big_int_Z.unit_big_int))
           (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
           Big_int_Z.unit_big_int)))))

  (** val sqrtrem : Big_int_Z.big_int -> Big_int_Z.big_int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 ->
        sqrtrem_step (fun x ->
          (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          x) (fun x ->
          (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big_int_Z.mult_int_big_int 2 x) (fun x ->
          (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          x) (sqrtrem p1))
        (fun _ -> (Big_int_Z.unit_big_int, (IsPos
        (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 ->
        sqrtrem_step (fun x ->
          (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          x) (fun x -> Big_int_Z.mult_int_big_int 2 x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big_int_Z.mult_int_big_int 2 x) (fun x ->
          Big_int_Z.mult_int_big_int 2 x) (sqrtrem p1))
        (fun _ -> (Big_int_Z.unit_big_int, (IsPos Big_int_Z.unit_big_int)))
        p0)
      (fun _ -> (Big_int_Z.unit_big_int, IsNul))
      p

  (** val sqrt : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sqrt p =
    fst (sqrtrem p)

  (** val coq_Nsucc_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_Nsucc_double x =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p ->
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val coq_Ndouble : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_Ndouble n =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      n

  (** val ldiff :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> Big_int_Z.zero_big_int)
        (fun _ -> Big_int_Z.unit_big_int)
        (fun _ -> Big_int_Z.zero_big_int)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_nat x =
    iter_op Nat0.add x (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred = (fun n -> Big_int_Z.max_big_int Big_int_Z.unit_big_int
  (Big_int_Z.pred_big_int n))

  (** val square : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec square p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (add (square p0) p0)))
      (fun p0 -> Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (square p0)))
      (fun _ -> Big_int_Z.unit_big_int)
      p

  (** val size_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> Big_int_Z.succ_big_int (size_nat p0))
      (fun p0 -> Big_int_Z.succ_big_int (size_nat p0))
      (fun _ -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
      p

  (** val size : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> Big_int_Z.unit_big_int)
      p

  (** val gcdn :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int **)

  let rec gcdn n a b =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 -> gcdn n0 a b0)
          (fun _ -> Big_int_Z.unit_big_int)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun _ -> gcdn n0 a0 b)
          (fun b0 -> Big_int_Z.mult_int_big_int 2 (gcdn n0 a0 b0))
          (fun _ -> Big_int_Z.unit_big_int)
          b)
        (fun _ -> Big_int_Z.unit_big_int)
        a)
      n

  (** val gcd :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let gcd a b =
    gcdn (Nat0.add (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> (Big_int_Z.unit_big_int, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (Big_int_Z.unit_big_int, Big_int_Z.unit_big_int))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in
            (g, (aa, (add aa (Big_int_Z.mult_int_big_int 2 ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in
            (g, ((add bb (Big_int_Z.mult_int_big_int 2 ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, (Big_int_Z.mult_int_big_int 2 bb))))
          (fun _ -> (Big_int_Z.unit_big_int, (a, Big_int_Z.unit_big_int)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, ((Big_int_Z.mult_int_big_int 2 aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in ((Big_int_Z.mult_int_big_int 2 g), p))
          (fun _ -> (Big_int_Z.unit_big_int, (a, Big_int_Z.unit_big_int)))
          b)
        (fun _ -> (Big_int_Z.unit_big_int, (Big_int_Z.unit_big_int, b)))
        a)
      n

  (** val ggcd :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let ggcd a b =
    ggcdn (Nat0.add (size_nat a) (size_nat b)) a b

  (** val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> true)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> false)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val of_uint_acc :
      Decimal.uint -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec of_uint_acc d acc =
    match d with
    | Decimal.Nil -> acc
    | Decimal.D0 l ->
      of_uint_acc l
        (mul (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc)
    | Decimal.D1 l ->
      of_uint_acc l
        (add Big_int_Z.unit_big_int
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D2 l ->
      of_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D3 l ->
      of_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D4 l ->
      of_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D5 l ->
      of_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D6 l ->
      of_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D7 l ->
      of_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D8 l ->
      of_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))
    | Decimal.D9 l ->
      of_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))) acc))

  (** val of_uint : Decimal.uint -> Big_int_Z.big_int **)

  let rec of_uint = function
  | Decimal.Nil -> Big_int_Z.zero_big_int
  | Decimal.D0 l -> of_uint l
  | Decimal.D1 l -> (of_uint_acc l Big_int_Z.unit_big_int)
  | Decimal.D2 l ->
    (of_uint_acc l (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))
  | Decimal.D3 l ->
    (of_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))
  | Decimal.D4 l ->
    (of_uint_acc l (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
  | Decimal.D5 l ->
    (of_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
  | Decimal.D6 l ->
    (of_uint_acc l (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))
  | Decimal.D7 l ->
    (of_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))
  | Decimal.D8 l ->
    (of_uint_acc l (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))
  | Decimal.D9 l ->
    (of_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))

  (** val of_hex_uint_acc : uint -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l ->
      of_hex_uint_acc l
        (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int)))) acc)
    | D1 l ->
      of_hex_uint_acc l
        (add Big_int_Z.unit_big_int
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D2 l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D3 l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D4 l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D5 l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D6 l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D7 l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D8 l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | D9 l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | Da l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | Db l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | Dc l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | Dd l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | De l ->
      of_hex_uint_acc l
        (add (Big_int_Z.mult_int_big_int 2
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))
    | Df l ->
      of_hex_uint_acc l
        (add
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
          Big_int_Z.unit_big_int)))
          (mul (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            Big_int_Z.unit_big_int)))) acc))

  (** val of_hex_uint : uint -> Big_int_Z.big_int **)

  let rec of_hex_uint = function
  | Nil -> Big_int_Z.zero_big_int
  | D0 l -> of_hex_uint l
  | D1 l -> (of_hex_uint_acc l Big_int_Z.unit_big_int)
  | D2 l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))
  | D3 l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))
  | D4 l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
  | D5 l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))
  | D6 l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))
  | D7 l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)))
  | D8 l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))
  | D9 l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      Big_int_Z.unit_big_int))))
  | Da l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))
  | Db l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))
  | Dc l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))
  | Dd l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))
  | De l ->
    (of_hex_uint_acc l (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))
  | Df l ->
    (of_hex_uint_acc l
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int))))

  (** val to_little_uint : Big_int_Z.big_int -> Decimal.uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> Decimal.Little.succ_double (to_little_uint p0))
      (fun p0 -> Decimal.Little.double (to_little_uint p0))
      (fun _ -> Decimal.D1 Decimal.Nil)
      p

  (** val to_uint : Big_int_Z.big_int -> Decimal.uint **)

  let to_uint p =
    Decimal.rev (to_little_uint p)

  (** val to_little_hex_uint : Big_int_Z.big_int -> uint **)

  let rec to_little_hex_uint p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> Little.succ_double (to_little_hex_uint p0))
      (fun p0 -> Little.double (to_little_hex_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_hex_uint : Big_int_Z.big_int -> uint **)

  let to_hex_uint p =
    rev (to_little_hex_uint p)

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end
