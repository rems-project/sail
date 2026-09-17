open BinInt
open BinNat
open Bit
open Bool
open Datatypes
open List0
open ListDef
open ListUtil
open PrimVector
open Definitions

(** val length : bvn -> Big_int_Z.big_int **)

let length x =
  Z.of_N x.bvn_n

(** val and_bit : bit -> bit -> bit **)

let and_bit x y =
  match x with
  | B0 -> B0
  | B1 -> y

(** val or_bit : bit -> bit -> bit **)

let or_bit x y =
  match x with
  | B0 -> y
  | B1 -> B1

(** val xor_bit : bit -> bit -> bit **)

let xor_bit x y =
  match x with
  | B0 -> y
  | B1 -> (match y with
           | B0 -> B1
           | B1 -> B0)

(** val not_bit : bit -> bit **)

let not_bit = function
| B0 -> B1
| B1 -> B0

(** val add_bit_with_carry : bit -> bit -> bit -> bit * bit **)

let add_bit_with_carry x y carry =
  match x with
  | B0 ->
    (match y with
     | B0 -> (match carry with
              | B0 -> (B0, B0)
              | B1 -> (B1, B0))
     | B1 -> (match carry with
              | B0 -> (B1, B0)
              | B1 -> (B0, B1)))
  | B1 ->
    (match y with
     | B0 -> (match carry with
              | B0 -> (B1, B0)
              | B1 -> (B0, B1))
     | B1 -> (match carry with
              | B0 -> (B0, B1)
              | B1 -> (B1, B1)))

(** val sub_bit_with_carry : bit -> bit -> bit -> bit * bit **)

let sub_bit_with_carry x y carry =
  match x with
  | B0 ->
    (match y with
     | B0 -> (match carry with
              | B0 -> (B0, B0)
              | B1 -> (B1, B0))
     | B1 -> (match carry with
              | B0 -> (B0, B1)
              | B1 -> (B0, B0)))
  | B1 ->
    (match y with
     | B0 -> (match carry with
              | B0 -> (B1, B0)
              | B1 -> (B1, B1))
     | B1 -> (match carry with
              | B0 -> (B0, B0)
              | B1 -> (B1, B0)))

(** val bool_of_bit : bit -> bool **)

let bool_of_bit =
  bit_to_bool

(** val bit_of_bool : bool -> bit **)

let bit_of_bool =
  bool_to_bit

(** val string_of_bit : bit -> string **)

let string_of_bit = function
| B0 -> "0"
| B1 -> "1"

(** val char_of_bit : bit -> char **)

let char_of_bit = function
| B0 -> '0'
| B1 -> '1'

(** val bigint_of_bit : bit -> Big_int_Z.big_int **)

let bigint_of_bit = function
| B0 -> Big_int_Z.zero_big_int
| B1 -> Big_int_Z.unit_big_int

(** val and_bool : bool -> bool -> bool **)

let and_bool =
  (&&)

(** val or_bool : bool -> bool -> bool **)

let or_bool =
  (||)

(** val xor_bool : bool -> bool -> bool **)

let xor_bool =
  xorb

(** val eq_bool : bool -> bool -> bool **)

let eq_bool =
  eqb

(** val of_bit_list : bit list -> bvn **)

let of_bit_list =
  Bits.to_bvn

(** val to_bit_list : bvn -> bit list **)

let to_bit_list x =
  map bool_to_bit (rev (bv_to_bits x.bvn_n x.bvn_val))

(** val width : bvn -> Big_int_Z.big_int **)

let width x =
  Z.of_N x.bvn_n

(** val bits_eqb : bit list -> bit list -> bool **)

let bits_eqb xs ys =
  list_eqb bit_eqb xs ys

(** val lift1 : (Big_int_Z.big_int -> bv -> bv) -> bvn -> bvn **)

let lift1 f x =
  { bvn_n = x.bvn_n; bvn_val = (f x.bvn_n x.bvn_val) }

(** val lift2 :
    (Big_int_Z.big_int -> bv -> bv -> bv) -> bvn -> bvn -> bvn option **)

let lift2 f x y =
  match bvn_to_bv x.bvn_n y with
  | Some y' -> Some { bvn_n = x.bvn_n; bvn_val = (f x.bvn_n x.bvn_val y') }
  | None -> None

(** val not_vec : bvn -> bvn **)

let not_vec x =
  lift1 bv_not x

(** val and_vec : bvn -> bvn -> bvn option **)

let and_vec x y =
  lift2 bv_and x y

(** val or_vec : bvn -> bvn -> bvn option **)

let or_vec x y =
  lift2 bv_or x y

(** val xor_vec : bvn -> bvn -> bvn option **)

let xor_vec x y =
  lift2 bv_xor x y

(** val uint : bvn -> Big_int_Z.big_int **)

let uint x =
  x.bvn_val.bv_unsigned

(** val sint : bvn -> Big_int_Z.big_int **)

let sint x =
  bv_signed x.bvn_n x.bvn_val

(** val zeros : Big_int_Z.big_int -> bvn **)

let zeros n =
  { bvn_n = (Z.to_N n); bvn_val = (bv_0 (Z.to_N n)) }

(** val ones : Big_int_Z.big_int -> bvn **)

let ones n =
  { bvn_n = (Z.to_N n); bvn_val = (bv_not (Z.to_N n) (bv_0 (Z.to_N n))) }

(** val zrange :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let zrange lo hi =
  map (fun k -> Z.add lo (Z.of_nat k))
    (seq Big_int_Z.zero_big_int (Big_int_Z.succ_big_int
      (Z.to_nat (Z.sub hi lo))))

(** val zero_extend : bvn -> Big_int_Z.big_int -> bvn **)

let zero_extend x n =
  { bvn_n = (Z.to_N n); bvn_val =
    (bv_zero_extend x.bvn_n (Z.to_N n) x.bvn_val) }

(** val sign_extend : bvn -> Big_int_Z.big_int -> bvn **)

let sign_extend x n =
  { bvn_n = (Z.to_N n); bvn_val =
    (bv_sign_extend x.bvn_n (Z.to_N n) x.bvn_val) }

(** val shiftr : bvn -> Big_int_Z.big_int -> bvn **)

let shiftr x y =
  { bvn_n = x.bvn_n; bvn_val =
    (coq_Z_to_bv x.bvn_n (Z.shiftr x.bvn_val.bv_unsigned y)) }

(** val shiftl : bvn -> Big_int_Z.big_int -> bvn **)

let shiftl x y =
  { bvn_n = x.bvn_n; bvn_val =
    (coq_Z_to_bv x.bvn_n (Z.shiftl x.bvn_val.bv_unsigned y)) }

(** val arith_shiftr : bvn -> Big_int_Z.big_int -> bvn **)

let arith_shiftr x y =
  { bvn_n = x.bvn_n; bvn_val =
    (coq_Z_to_bv x.bvn_n (Z.shiftr (bv_signed x.bvn_n x.bvn_val) y)) }

(** val shiftr_ref : bit list -> Big_int_Z.big_int -> bit list **)

let shiftr_ref xs y =
  take (Z.of_nat (Datatypes.length xs)) (app (repeat B0 (Z.to_nat y)) xs)

(** val shiftl_ref : bit list -> Big_int_Z.big_int -> bit list **)

let shiftl_ref xs y =
  drop y (app xs (repeat B0 (Z.to_nat y)))

(** val arith_shiftr_ref : bit list -> Big_int_Z.big_int -> bit list **)

let arith_shiftr_ref xs y =
  take (Z.of_nat (Datatypes.length xs))
    (app (concat (repeat (take Big_int_Z.unit_big_int xs) (Z.to_nat y))) xs)

(** val shift_bits_right : bvn -> bvn -> bvn **)

let shift_bits_right x y =
  shiftr x (uint y)

(** val shift_bits_left : bvn -> bvn -> bvn **)

let shift_bits_left x y =
  shiftl x (uint y)

(** val shift_bits_right_arith : bvn -> bvn -> bvn **)

let shift_bits_right_arith x y =
  arith_shiftr x (uint y)

(** val get_slice_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let get_slice_int n m o =
  { bvn_n = (Z.to_N n); bvn_val = (coq_Z_to_bv (Z.to_N n) (Z.shiftr m o)) }

(** val to_bits : Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let to_bits len n =
  { bvn_n = (Z.to_N len); bvn_val = (coq_Z_to_bv (Z.to_N len) n) }

(** val get_slice_int_ref_aux :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bit list **)

let rec get_slice_int_ref_aux k m o =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun k0 ->
    (if Z.testbit m (Z.add (Z.of_nat k0) o) then B1 else B0) :: (get_slice_int_ref_aux
                                                                  k0 m o))
    k

(** val get_slice_int_ref :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bit list **)

let get_slice_int_ref n m o =
  get_slice_int_ref_aux (Z.to_nat n) m o

(** val to_bits_ref : Big_int_Z.big_int -> Big_int_Z.big_int -> bit list **)

let to_bits_ref len n =
  get_slice_int_ref len n Big_int_Z.zero_big_int

(** val add_vec : bvn -> bvn -> bvn option **)

let add_vec x y =
  lift2 bv_add x y

(** val sub_vec : bvn -> bvn -> bvn option **)

let sub_vec x y =
  lift2 bv_sub x y

(** val add_vec_int : bvn -> Big_int_Z.big_int -> bvn **)

let add_vec_int x n =
  { bvn_n = x.bvn_n; bvn_val = (bv_add_Z x.bvn_n x.bvn_val n) }

(** val sub_vec_int : bvn -> Big_int_Z.big_int -> bvn **)

let sub_vec_int x n =
  { bvn_n = x.bvn_n; bvn_val = (bv_sub_Z x.bvn_n x.bvn_val n) }

(** val count_leading_zeros : bvn -> Big_int_Z.big_int **)

let count_leading_zeros x =
  let v = x.bvn_val.bv_unsigned in
  if Z.eqb v Big_int_Z.zero_big_int
  then width x
  else Z.sub (width x) (Z.add (Z.log2 v) Big_int_Z.unit_big_int)

(** val count_trailing_zeros : bvn -> Big_int_Z.big_int **)

let count_trailing_zeros x =
  let v = x.bvn_val.bv_unsigned in
  if Z.eqb v Big_int_Z.zero_big_int
  then width x
  else Z.log2 (Z.coq_land v (Z.opp v))

(** val count_leading_zeros_ref : bit list -> Big_int_Z.big_int **)

let rec count_leading_zeros_ref = function
| [] -> Big_int_Z.zero_big_int
| b :: xs0 ->
  (match b with
   | B0 -> Z.add Big_int_Z.unit_big_int (count_leading_zeros_ref xs0)
   | B1 -> Big_int_Z.zero_big_int)

(** val count_trailing_zeros_ref : bit list -> Big_int_Z.big_int **)

let count_trailing_zeros_ref xs =
  count_leading_zeros_ref (rev xs)

(** val append : bvn -> bvn -> bvn **)

let append x y =
  { bvn_n = (N.add x.bvn_n y.bvn_n); bvn_val =
    (bv_concat (N.add x.bvn_n y.bvn_n) x.bvn_n y.bvn_n x.bvn_val y.bvn_val) }

(** val eq_bits : bvn -> bvn -> bool **)

let eq_bits x y =
  (&&) (N.eqb x.bvn_n y.bvn_n)
    (Z.eqb x.bvn_val.bv_unsigned y.bvn_val.bv_unsigned)

(** val mult_vec : bvn -> bvn -> bvn **)

let mult_vec x y =
  to_bits
    (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) (width x))
    (Z.mul (uint x) (uint y))

(** val mults_vec : bvn -> bvn -> bvn **)

let mults_vec x y =
  to_bits
    (Z.mul (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) (width x))
    (Z.mul (sint x) (sint y))

(** val subrange : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let subrange x n m =
  { bvn_n = (Z.to_N (Z.add (Z.sub n m) Big_int_Z.unit_big_int)); bvn_val =
    (bv_extract x.bvn_n (Z.to_N m)
      (Z.to_N (Z.add (Z.sub n m) Big_int_Z.unit_big_int)) x.bvn_val) }

(** val slice : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let slice x n m =
  { bvn_n = (Z.to_N m); bvn_val =
    (bv_extract x.bvn_n (Z.to_N n) (Z.to_N m) x.bvn_val) }

(** val access : bvn -> Big_int_Z.big_int -> bvn **)

let access x n =
  { bvn_n = Big_int_Z.unit_big_int; bvn_val =
    (bv_extract x.bvn_n (Z.to_N n) Big_int_Z.unit_big_int x.bvn_val) }

(** val update_bit : bvn -> Big_int_Z.big_int -> bit -> bvn **)

let update_bit x n b =
  let v = x.bvn_val.bv_unsigned in
  { bvn_n = x.bvn_n; bvn_val =
  (coq_Z_to_bv x.bvn_n
    (if bit_to_bool b
     then Z.coq_lor v (Z.shiftl Big_int_Z.unit_big_int n)
     else Z.coq_land v (Z.lnot (Z.shiftl Big_int_Z.unit_big_int n)))) }

(** val update_subrange :
    bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn -> bvn **)

let update_subrange x n m y =
  let w = Z.add (Z.sub n m) Big_int_Z.unit_big_int in
  let mask = Z.shiftl (Z.pred (Z.shiftl Big_int_Z.unit_big_int w)) m in
  { bvn_n = x.bvn_n; bvn_val =
  (coq_Z_to_bv x.bvn_n
    (Z.coq_lor (Z.coq_land x.bvn_val.bv_unsigned (Z.lnot mask))
      (Z.shiftl
        (Z.coq_land (uint y) (Z.pred (Z.shiftl Big_int_Z.unit_big_int w))) m))) }

(** val set_slice : bvn -> Big_int_Z.big_int -> bvn -> bvn **)

let set_slice out n slice0 =
  update_subrange out (Z.sub (Z.add n (width slice0)) Big_int_Z.unit_big_int)
    n slice0

(** val set_slice_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn ->
    Big_int_Z.big_int **)

let set_slice_int slice_len m n slice0 =
  let mask = Z.shiftl (Z.pred (Z.shiftl Big_int_Z.unit_big_int slice_len)) n
  in
  Z.coq_lor (Z.coq_land m (Z.lnot mask)) (Z.shiftl (uint slice0) n)

(** val set_slice_int_ref :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn ->
    Big_int_Z.big_int **)

let set_slice_int_ref slice_len m n slice0 =
  let mask = Z.shiftl (Z.pred (Z.shiftl Big_int_Z.unit_big_int slice_len)) n
  in
  Z.coq_lor (Z.coq_lxor (Z.coq_lor mask m) mask) (Z.shiftl (uint slice0) n)

(** val subrange_inc :
    bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let subrange_inc x n m =
  subrange x (Z.sub (Z.sub (width x) Big_int_Z.unit_big_int) n)
    (Z.sub (Z.sub (width x) Big_int_Z.unit_big_int) m)

(** val slice_inc : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn **)

let slice_inc x n m =
  subrange x (Z.sub (Z.sub (width x) Big_int_Z.unit_big_int) n)
    (Z.sub (Z.sub (width x) m) n)

(** val access_inc : bvn -> Big_int_Z.big_int -> bvn **)

let access_inc x n =
  access x (Z.sub (Z.sub (width x) Big_int_Z.unit_big_int) n)

(** val update_bit_inc : bvn -> Big_int_Z.big_int -> bit -> bvn **)

let update_bit_inc x n b =
  update_bit x (Z.sub (Z.sub (width x) Big_int_Z.unit_big_int) n) b

(** val add_vec_carry : bvn -> bvn -> (bit * bvn) option **)

let add_vec_carry x y =
  match add_vec x y with
  | Some sum ->
    let carry =
      Z.leb
        (Z.pow (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
          (width x))
        (Z.add (uint x) (uint y))
    in
    Some ((bool_to_bit carry), sum)
  | None -> None

(** val replicate_bits_aux : Big_int_Z.big_int -> bvn -> bvn -> bvn **)

let rec replicate_bits_aux k x acc =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> acc)
    (fun k0 -> replicate_bits_aux k0 x (append acc x))
    k

(** val replicate_bits : bvn -> Big_int_Z.big_int -> bvn **)

let replicate_bits x n =
  replicate_bits_aux (Z.to_nat n) x (zeros Big_int_Z.zero_big_int)

(** val vector_truncate : bvn -> Big_int_Z.big_int -> bvn **)

let vector_truncate x n =
  { bvn_n = (Z.to_N n); bvn_val =
    (bv_zero_extend x.bvn_n (Z.to_N n) x.bvn_val) }

(** val vector_truncateLSB : bvn -> Big_int_Z.big_int -> bvn **)

let vector_truncateLSB x n =
  subrange x (Z.sub (width x) Big_int_Z.unit_big_int) (Z.sub (width x) n)

(** val reverse_endianness_fuel : Big_int_Z.big_int -> bvn -> bvn **)

let rec reverse_endianness_fuel fuel x =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> x)
    (fun fuel0 ->
    if Z.leb (width x) (Big_int_Z.mult_int_big_int 2
         (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
         Big_int_Z.unit_big_int)))
    then x
    else append
           (reverse_endianness_fuel fuel0
             (subrange x
               (Z.sub (width x)
                 ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
                 (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
                 Big_int_Z.unit_big_int))))
               Big_int_Z.zero_big_int))
           (subrange x (Z.sub (width x) Big_int_Z.unit_big_int)
             (Z.sub (width x) (Big_int_Z.mult_int_big_int 2
               (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
               Big_int_Z.unit_big_int))))))
    fuel

(** val reverse_endianness : bvn -> bvn **)

let reverse_endianness x =
  reverse_endianness_fuel (N.to_nat x.bvn_n) x

(** val split_at : Big_int_Z.big_int -> bvn -> bvn * bvn **)

let split_at s x =
  let w = width x in
  let k = Z.max Big_int_Z.zero_big_int (Z.min s w) in
  ((subrange x (Z.sub w Big_int_Z.unit_big_int) (Z.sub w k)),
  (subrange x (Z.sub (Z.sub w k) Big_int_Z.unit_big_int)
    Big_int_Z.zero_big_int))

(** val to_single_bits : bvn -> bvn list **)

let to_single_bits x =
  map (fun b -> of_bit_list (b :: [])) (to_bit_list x)
