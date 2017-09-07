type uint32 = Nat_big_num.num

(* 2^32 - 1 *)
let max_int =
  Nat_big_num.of_string "4294967295"
;;

let add l r =
  Nat_big_num.modulus (Nat_big_num.add l r) max_int
;;

let of_char (c : char) : uint32 =
  Nat_big_num.of_int (Char.code c)
;;

let of_int (i : int) =
  Nat_big_num.of_int i
;;

let of_bigint (i : Nat_big_num.num) : uint32 =
  Nat_big_num.modulus i max_int
;;

let of_int32 (i : Int32.t) =
  Nat_big_num.of_int32 i
;;

let to_bigint (u : uint32) : Nat_big_num.num = u
;;

let shift_left i s =
  Nat_big_num.modulus (Nat_big_num.shift_left i s) max_int
;;

let shift_right i s =
  Nat_big_num.modulus (Nat_big_num.shift_right i s) max_int
;;

let logand l r =
  Nat_big_num.modulus (Nat_big_num.bitwise_and l r) max_int
;;

let logor l r =
  Nat_big_num.modulus (Nat_big_num.bitwise_or l r) max_int
;;

let to_string l =
  Nat_big_num.to_string l
;;

let to_char u =
  Char.chr (Nat_big_num.to_int u)
;;

let equal l r =
  Nat_big_num.equal l r
;;

let of_quad c1 c2 c3 c4 =
  let b1 = Nat_big_num.of_int (Char.code c1) in
  let b2 = shift_left (Nat_big_num.of_int (Char.code c2)) 8 in
  let b3 = shift_left (Nat_big_num.of_int (Char.code c3)) 16 in
  let b4 = shift_left (Nat_big_num.of_int (Char.code c4)) 24 in
    Nat_big_num.add b1 (Nat_big_num.add b2 (Nat_big_num.add b3 b4))
;;

let of_quad_native c1 c2 c3 c4 =
  let b1 = Uint32.of_int (Char.code c1) in
  let b2 = Uint32.shift_left (Uint32.of_int (Char.code c2)) 8 in
  let b3 = Uint32.shift_left (Uint32.of_int (Char.code c3)) 16 in
  let b4 = Uint32.shift_left (Uint32.of_int (Char.code c4)) 24 in
    Uint32.add b1 (Uint32.add b2 (Uint32.add b3 b4))
;;

let of_dual_native c1 c2 = of_quad_native c1 c2 '\000' '\000'
;;

let to_bytes u : char * char * char * char =
  let b0 = Char.chr (Nat_big_num.to_int (logand u (Nat_big_num.of_string "255"))) in
  let b1 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "65280")) 8)) in
  let b2 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "16711680")) 16)) in
  let b3 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "4278190080")) 24)) in
    b0, b1, b2, b3
;;

let to_bytes_native u : char * char * char * char =
  let b0 = Char.chr (Uint32.to_int (Uint32.logand u (Uint32.of_string "255"))) in
  let b1 = Char.chr (Uint32.to_int (Uint32.shift_right (Uint32.logand u (Uint32.of_string "65280")) 8)) in
  let b2 = Char.chr (Uint32.to_int (Uint32.shift_right (Uint32.logand u (Uint32.of_string "16711680")) 16)) in
  let b3 = Char.chr (Uint32.to_int (Uint32.shift_right (Uint32.logand u (Uint32.of_string "4278190080")) 24)) in
    b0, b1, b2, b3
;;

let to_dual_bytes_native u : char * char =
  let (b3, b2, b1, b0) = to_bytes_native u in
    b3, b2
;;
