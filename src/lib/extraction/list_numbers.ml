open BinInt
open ListDef
open Base
open List_monad

module Coq_list =
 struct
  (** val seqZ :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

  let seqZ m len =
    fmap (Obj.magic (fun _ _ -> Coq_list.list_fmap)) (fun i ->
      Z.add (Z.of_nat i) m)
      (Obj.magic seq Big_int_Z.zero_big_int (Z.to_nat len))
 end
