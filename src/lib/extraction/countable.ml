open BinNat
open BinPos
open Base
open Numbers
open Option

type 'a coq_Countable = { encode : ('a -> Big_int_Z.big_int);
                          decode : (Big_int_Z.big_int -> 'a option) }

(** val coq_N_countable : Big_int_Z.big_int coq_Countable **)

let coq_N_countable =
  { encode = (fun x ->
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> BinPos.Pos.succ p)
      x);
    decode = (fun p ->
    if decide (decide_rel Pos.eq_dec p Big_int_Z.unit_big_int)
    then Some Big_int_Z.zero_big_int
    else Some (BinPos.Pos.pred p)) }

(** val nat_countable : Big_int_Z.big_int coq_Countable **)

let nat_countable =
  { encode = (fun x -> coq_N_countable.encode (BinNat.N.of_nat x)); decode =
    (fun p ->
    fmap (Obj.magic (fun _ _ -> option_fmap)) BinNat.N.to_nat
      ((Obj.magic coq_N_countable).decode p)) }
