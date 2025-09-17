open BinNums
open BinPos
open Datatypes
open PosDef

module N =
 struct
  (** val compare : coq_N -> coq_N -> comparison **)

  let compare n m =
    match n with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val add : coq_N -> coq_N -> coq_N **)

  let add n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (BinPos.Pos.add p q))

  (** val mul : coq_N -> coq_N -> coq_N **)

  let mul n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (BinPos.Pos.mul p q))
 end
