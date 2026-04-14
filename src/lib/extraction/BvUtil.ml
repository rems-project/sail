open BinNat
open BinPos
open Datatypes
open Nat0
open Definitions

module BoolList =
 struct
  (** val add_lsb :
      bool -> Big_int_Z.big_int option -> Big_int_Z.big_int option **)

  let add_lsb b prefix =
    if b
    then (match prefix with
          | Some n ->
            Some
              ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              n)
          | None -> Some Big_int_Z.unit_big_int)
    else (match prefix with
          | Some n -> Some (Big_int_Z.mult_int_big_int 2 n)
          | None -> None)

  (** val bits_to_N :
      bool list -> Big_int_Z.big_int option -> Big_int_Z.big_int **)

  let rec bits_to_N x acc =
    match x with
    | [] -> (match acc with
             | Some n -> n
             | None -> Big_int_Z.zero_big_int)
    | b :: x0 -> bits_to_N x0 (add_lsb b acc)

  (** val to_Z_unsigned :
      bool list -> Big_int_Z.big_int option -> Big_int_Z.big_int **)

  let to_Z_unsigned x prefix =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n -> n)
      (bits_to_N x prefix)

  (** val prefix_size : Big_int_Z.big_int option -> Big_int_Z.big_int **)

  let prefix_size = function
  | Some p -> Pos.size_nat p
  | None -> Big_int_Z.zero_big_int

  (** val to_bv' : bool list -> Big_int_Z.big_int option -> bv **)

  let to_bv' x prefix =
    coq_Z_to_bv (N.of_nat (add (prefix_size prefix) (length x)))
      (to_Z_unsigned x prefix)

  (** val to_bv : bool list -> bv **)

  let to_bv x =
    to_bv' x None
 end
