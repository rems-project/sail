open BinNat
open BinPos
open Bool
open Datatypes
open DecidableClass
open Decimal
open Hexadecimal
open NatDef
open Number
open PosDef

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Z =
 struct
  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 p))
      x

  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p ->
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p))
      (fun p -> Big_int_Z.minus_big_int (Pos.pred_double p))
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      (fun p -> (Pos.pred_double p))
      (fun p -> Big_int_Z.minus_big_int
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val pos_sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2
        q))
        (fun q -> Big_int_Z.minus_big_int (Pos.pred_double q))
        (fun _ -> Big_int_Z.zero_big_int)
        y)
      x

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp = Big_int_Z.minus_big_int

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = Big_int_Z.sub_big_int

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul = Big_int_Z.mult_big_int

  (** val pow_pos :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pow_pos z =
    Pos.iter (mul z) Big_int_Z.unit_big_int

  (** val pow :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pow x y =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> pow_pos x p)
      (fun _ -> Big_int_Z.zero_big_int)
      y

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb = Big_int_Z.eq_big_int

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let max = Big_int_Z.max_big_int

  (** val min :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let min = Big_int_Z.min_big_int

  (** val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_nat z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> Pos.to_nat p)
      (fun _ -> Big_int_Z.zero_big_int)
      z

  (** val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_nat n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n0 -> (Pos.of_succ_nat n0))
      n

  (** val of_N : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_N = (fun p -> p)

  (** val to_pos : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_pos z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> p)
      (fun _ -> Big_int_Z.unit_big_int)
      z

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
      let r' =
        add (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r)
          Big_int_Z.unit_big_int
      in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q), r')
      else ((add
              (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q)
              Big_int_Z.unit_big_int),
             (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) r in
      if ltb r' b
      then ((mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q), r')
      else ((add
              (mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) q)
              Big_int_Z.unit_big_int),
             (sub r' b)))
      (fun _ ->
      if leb (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) b
      then (Big_int_Z.zero_big_int, Big_int_Z.unit_big_int)
      else (Big_int_Z.unit_big_int, Big_int_Z.zero_big_int))
      a

  (** val div_eucl :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let div_eucl = Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> (zero_big_int, x)
  | 1 -> quomod_big_int x y
  | _ -> let (q, r) = quomod_big_int (add_int_big_int (-1) x) y in
          (add_int_big_int (-1) q, add_big_int (add_int_big_int 1 y) r))

  (** val div :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div = Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> zero_big_int
  | 1 -> div_big_int x y
  | _ -> add_int_big_int (-1) (div_big_int (add_int_big_int (-1) x) y))

  (** val modulo :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let modulo = Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> x
  | 1 -> mod_big_int x y
  | _ -> add_big_int y (add_int_big_int 1 (mod_big_int (add_int_big_int (-1) x) y)))

  (** val quotrem :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let quotrem a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> (Big_int_Z.zero_big_int, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> (Big_int_Z.zero_big_int, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a

  (** val quot :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let quot a b =
    fst (quotrem a b)

  (** val rem :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rem a b =
    snd (quotrem a b)

  (** val even : Big_int_Z.big_int -> bool **)

  let even z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      z

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div2 z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> (Pos.div2 p))
        (fun _ -> (Pos.div2 p))
        (fun _ -> Big_int_Z.zero_big_int)
        p)
      (fun p -> Big_int_Z.minus_big_int (Pos.div2_up p))
      z

  (** val sqrtrem :
      Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

  let sqrtrem n =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
      (fun p ->
      let (s, m) = Pos.sqrtrem p in
      (match m with
       | Pos.IsPos r -> (s, r)
       | _ -> (s, Big_int_Z.zero_big_int)))
      (fun _ -> (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int))
      n

  (** val shiftl :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let shiftl = Big_int_Z.(fun x y ->
  let y = int_of_big_int y in
  if y < 0 then shift_right_big_int x (-y)
  else shift_left_big_int x y)

  (** val shiftr :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let shiftr = Big_int_Z.(fun x y ->
  let y = int_of_big_int y in
  if y < 0 then shift_left_big_int x (-y)
  else shift_right_big_int x y)

  (** val coq_lor :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lor a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> (Pos.coq_lor a0 b0))
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.ldiff (Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.ldiff (Pos.pred_N a0) b0)))
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_land :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_land a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> Big_int_Z.zero_big_int)
        (fun b0 -> of_N (Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> Big_int_Z.zero_big_int)
        (fun b0 -> of_N (N.ldiff b0 (Pos.pred_N a0)))
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_lxor :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lxor a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> of_N (Pos.coq_lxor a0 b0))
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.coq_lxor a0 (Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> Big_int_Z.minus_big_int
        (N.succ_pos (N.coq_lxor (Pos.pred_N a0) b0)))
        (fun b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))
        b)
      a

  type t = Big_int_Z.big_int

  (** val zero : Big_int_Z.big_int **)

  let zero =
    Big_int_Z.zero_big_int

  (** val one : Big_int_Z.big_int **)

  let one =
    Big_int_Z.unit_big_int

  (** val two : Big_int_Z.big_int **)

  let two =
    (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)

  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ = Big_int_Z.succ_big_int

  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred = Big_int_Z.pred_big_int

  (** val square : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let square x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (BinPos.Pos.square p))
      (fun p -> (BinPos.Pos.square p))
      x

  (** val sgn : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sgn z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      z

  (** val geb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true

  (** val gtb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val abs : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let abs = Big_int_Z.abs_big_int

  (** val abs_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let abs_nat z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> BinPos.Pos.to_nat p)
      (fun p -> BinPos.Pos.to_nat p)
      z

  (** val abs_N : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let abs_N = Big_int_Z.abs_big_int

  (** val to_N : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_N = Big_int_Z.(fun p -> if sign_big_int p < 0 then zero_big_int else p)

  (** val of_uint : Decimal.uint -> Big_int_Z.big_int **)

  let of_uint d =
    of_N (BinPos.Pos.of_uint d)

  (** val of_hex_uint : Hexadecimal.uint -> Big_int_Z.big_int **)

  let of_hex_uint d =
    of_N (BinPos.Pos.of_hex_uint d)

  (** val of_num_uint : uint -> Big_int_Z.big_int **)

  let of_num_uint = function
  | UIntDecimal d0 -> of_uint d0
  | UIntHexadecimal d0 -> of_hex_uint d0

  (** val of_int : Decimal.signed_int -> Big_int_Z.big_int **)

  let of_int = function
  | Decimal.Pos d0 -> of_uint d0
  | Decimal.Neg d0 -> opp (of_uint d0)

  (** val of_hex_int : Hexadecimal.signed_int -> Big_int_Z.big_int **)

  let of_hex_int = function
  | Pos d0 -> of_hex_uint d0
  | Neg d0 -> opp (of_hex_uint d0)

  (** val of_num_int : signed_int -> Big_int_Z.big_int **)

  let of_num_int = function
  | IntDecimal d0 -> of_int d0
  | IntHexadecimal d0 -> of_hex_int d0

  (** val to_int : Big_int_Z.big_int -> Decimal.signed_int **)

  let to_int n =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Decimal.Pos (Decimal.D0 Decimal.Nil))
      (fun p -> Decimal.Pos (BinPos.Pos.to_uint p))
      (fun p -> Decimal.Neg (BinPos.Pos.to_uint p))
      n

  (** val to_hex_int : Big_int_Z.big_int -> Hexadecimal.signed_int **)

  let to_hex_int n =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Pos (D0 Nil))
      (fun p -> Pos (BinPos.Pos.to_hex_uint p))
      (fun p -> Neg (BinPos.Pos.to_hex_uint p))
      n

  (** val to_num_int : Big_int_Z.big_int -> signed_int **)

  let to_num_int n =
    IntDecimal (to_int n)

  (** val to_num_hex_int : Big_int_Z.big_int -> signed_int **)

  let to_num_hex_int n =
    IntHexadecimal (to_hex_int n)

  (** val iter : Big_int_Z.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n f x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> x)
      (fun p -> BinPos.Pos.iter f x p)
      (fun _ -> x)
      n

  (** val odd : Big_int_Z.big_int -> bool **)

  let odd z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      z

  (** val quot2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let quot2 z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> (BinPos.Pos.div2 p))
        (fun _ -> (BinPos.Pos.div2 p))
        (fun _ -> Big_int_Z.zero_big_int)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> Big_int_Z.minus_big_int (BinPos.Pos.div2 p))
        (fun _ -> Big_int_Z.minus_big_int (BinPos.Pos.div2 p))
        (fun _ -> Big_int_Z.zero_big_int)
        p)
      z

  (** val log2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let log2 z =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p -> (BinPos.Pos.size p))
        (fun p -> (BinPos.Pos.size p))
        (fun _ -> Big_int_Z.zero_big_int)
        p0)
      (fun _ -> Big_int_Z.zero_big_int)
      z

  (** val sqrt : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sqrt n =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (BinPos.Pos.sqrt p))
      (fun _ -> Big_int_Z.zero_big_int)
      n

  (** val gcd :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let gcd a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> abs b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> abs a)
        (fun b0 -> (BinPos.Pos.gcd a0 b0))
        (fun b0 -> (BinPos.Pos.gcd a0 b0))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> abs a)
        (fun b0 -> (BinPos.Pos.gcd a0 b0))
        (fun b0 -> (BinPos.Pos.gcd a0 b0))
        b)
      a

  (** val ggcd :
      Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int) **)

  let ggcd a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> ((abs b), (Big_int_Z.zero_big_int, (sgn b))))
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> ((abs a), ((sgn a), Big_int_Z.zero_big_int)))
        (fun b0 ->
        let (g, p) = BinPos.Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = BinPos.Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, (Big_int_Z.minus_big_int bb))))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> ((abs a), ((sgn a), Big_int_Z.zero_big_int)))
        (fun b0 ->
        let (g, p) = BinPos.Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big_int_Z.minus_big_int aa), bb)))
        (fun b0 ->
        let (g, p) = BinPos.Pos.ggcd a0 b0 in
        let (aa, bb) = p in
        (g, ((Big_int_Z.minus_big_int aa), (Big_int_Z.minus_big_int bb))))
        b)
      a

  (** val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let testbit a n =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> odd a)
      (fun p ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> false)
        (fun a0 -> BinPos.Pos.testbit a0 p)
        (fun a0 -> negb (BinNat.N.testbit (BinPos.Pos.pred_N a0) p))
        a)
      (fun _ -> false)
      n

  (** val ldiff :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let ldiff a b =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> of_N (BinPos.Pos.ldiff a0 b0))
        (fun b0 -> of_N (BinNat.N.coq_land a0 (BinPos.Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
        (fun _ -> a)
        (fun b0 -> Big_int_Z.minus_big_int
        (BinNat.N.succ_pos (BinNat.N.coq_lor (BinPos.Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (BinNat.N.ldiff (BinPos.Pos.pred_N b0) (BinPos.Pos.pred_N a0)))
        b)
      a

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec = Big_int_Z.eq_big_int

  module Private_BootStrap =
   struct
   end

  (** val coq_Decidable_eq_Z :
      Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable **)

  let coq_Decidable_eq_Z x y =
    { coq_Decidable_witness = (eqb x y) }

  (** val coq_Decidable_lt_Z :
      Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable **)

  let coq_Decidable_lt_Z x y =
    { coq_Decidable_witness = (ltb x y) }

  (** val coq_Decidable_le_Z :
      Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable **)

  let coq_Decidable_le_Z x y =
    { coq_Decidable_witness = (leb x y) }

  (** val coq_Decidable_gt_Z :
      Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable **)

  let coq_Decidable_gt_Z x y =
    { coq_Decidable_witness = (gtb x y) }

  (** val coq_Decidable_ge_Z :
      Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable **)

  let coq_Decidable_ge_Z x y =
    { coq_Decidable_witness = (geb x y) }

  (** val leb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  (** val measure_right_induction :
      ('a1 -> Big_int_Z.big_int) -> Big_int_Z.big_int -> ('a1 -> __ -> ('a1
      -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

  let measure_right_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_left_induction :
      ('a1 -> Big_int_Z.big_int) -> Big_int_Z.big_int -> ('a1 -> __ -> ('a1
      -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

  let measure_left_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
        Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
        Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
        Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
        Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case :
      Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case :
      Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  (** val sqrt_up : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sqrt_up a =
    match compare Big_int_Z.zero_big_int a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Big_int_Z.zero_big_int

  (** val log2_up : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let log2_up a =
    match compare Big_int_Z.unit_big_int a with
    | Lt -> succ (log2 (pred a))
    | _ -> Big_int_Z.zero_big_int

  module Private_NZDiv =
   struct
   end

  module Private_Div =
   struct
    module Quot2Div =
     struct
      (** val div :
          Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

      let div =
        quot

      (** val modulo :
          Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

      let modulo =
        rem
     end

    module NZQuot =
     struct
     end
   end

  (** val lcm :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let lcm a b =
    abs (mul a (div b (gcd a b)))

  (** val eqb_spec : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2z : bool -> Big_int_Z.big_int **)

  let b2z = function
  | true -> Big_int_Z.unit_big_int
  | false -> Big_int_Z.zero_big_int

  (** val setbit :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let setbit a n =
    coq_lor a (shiftl Big_int_Z.unit_big_int n)

  (** val clearbit :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let clearbit a n =
    ldiff a (shiftl Big_int_Z.unit_big_int n)

  (** val lnot : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let lnot a =
    pred (opp a)

  (** val ones : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let ones n =
    pred (shiftl Big_int_Z.unit_big_int n)
 end
