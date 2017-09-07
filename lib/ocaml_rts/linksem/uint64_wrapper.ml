type uint64
  = Nat_big_num.num

(* 2^64 - 1 *)
let max_int =
  let x = Nat_big_num.of_string "4294967296" in
  let y = Nat_big_num.mul x (Nat_big_num.of_int 2) in
    Nat_big_num.sub y (Nat_big_num.of_int 1)
;;

let add l r =
  Nat_big_num.modulus (Nat_big_num.add l r) max_int
;;

let minus l r =
  Nat_big_num.modulus (Nat_big_num.sub l r) max_int
;;

let of_int i =
  Nat_big_num.of_int i
;;

let of_int64 (i : Int64.t) =
  Nat_big_num.of_int64 i
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

let equal l r =
  Nat_big_num.equal l r
;;

let of_oct c1 c2 c3 c4 c5 c6 c7 c8 =
  let b1 = Nat_big_num.of_int (Char.code c1) in
  let b2 = shift_left (Nat_big_num.of_int (Char.code c2)) 8 in
  let b3 = shift_left (Nat_big_num.of_int (Char.code c3)) 16 in
  let b4 = shift_left (Nat_big_num.of_int (Char.code c4)) 24 in
  let b5 = shift_left (Nat_big_num.of_int (Char.code c5)) 32 in
  let b6 = shift_left (Nat_big_num.of_int (Char.code c6)) 40 in
  let b7 = shift_left (Nat_big_num.of_int (Char.code c7)) 48 in
  let b8 = shift_left (Nat_big_num.of_int (Char.code c8)) 56 in
    Nat_big_num.add b1 (Nat_big_num.add b2
      (Nat_big_num.add b3 (Nat_big_num.add b4
        (Nat_big_num.add b5 (Nat_big_num.add b6
          (Nat_big_num.add b7 b8))))))
;;

let of_oct_native c1 c2 c3 c4 c5 c6 c7 c8 =
  let b1 = Uint64.of_int (Char.code c1) in
  let b2 = Uint64.shift_left (Uint64.of_int (Char.code c2)) 8 in
  let b3 = Uint64.shift_left (Uint64.of_int (Char.code c3)) 16 in
  let b4 = Uint64.shift_left (Uint64.of_int (Char.code c4)) 24 in
  let b5 = Uint64.shift_left (Uint64.of_int (Char.code c5)) 32 in
  let b6 = Uint64.shift_left (Uint64.of_int (Char.code c6)) 40 in
  let b7 = Uint64.shift_left (Uint64.of_int (Char.code c7)) 48 in
  let b8 = Uint64.shift_left (Uint64.of_int (Char.code c8)) 56 in
    Uint64.add b1 (Uint64.add b2
      (Uint64.add b3 (Uint64.add b4
        (Uint64.add b5 (Uint64.add b6
          (Uint64.add b7 b8))))))
;;

let to_bigint (u : uint64) : Nat_big_num.num =
  u
;;

let of_bigint (u : Nat_big_num.num) : uint64 =
  Nat_big_num.modulus u max_int
;;

let to_bytes u : char * char * char * char * char * char * char * char =
  let u1 = Nat_big_num.mul (Nat_big_num.of_string "4278190080") (Nat_big_num.of_string "255") in (* 0xFF00000000 *)
  let u2 = Nat_big_num.mul (Nat_big_num.of_string "4278190080") (Nat_big_num.of_string "65280") in (* 0xFF0000000000 *)
  let u3 = Nat_big_num.mul (Nat_big_num.of_string "4278190080") (Nat_big_num.of_string "16711680") in (* 0xFF000000000000 *)
  let u4 = Nat_big_num.mul (Nat_big_num.of_string "4278190080") (Nat_big_num.of_string "4278190080") in (* 0xFF00000000000000 *)
  let b0 = Char.chr (Nat_big_num.to_int (logand u (Nat_big_num.of_string "255"))) in (* 0xFF *)
  let b1 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "65280")) 8)) in (* 0xFF00 *)
  let b2 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "16711680")) 16)) in (* 0xFF0000 *)
  let b3 = Char.chr (Nat_big_num.to_int (shift_right (logand u (Nat_big_num.of_string "4278190080")) 24)) in (* 0xFF000000 *)
  let b4 = Char.chr (Nat_big_num.to_int (shift_right (logand u u1) 32)) in (* 0xFF00000000 *)
  let b5 = Char.chr (Nat_big_num.to_int (shift_right (logand u u2) 40)) in (* 0xFF0000000000 *)
  let b6 = Char.chr (Nat_big_num.to_int (shift_right (logand u u3) 48)) in (* 0xFF000000000000 *)
  let b7 = Char.chr (Nat_big_num.to_int (shift_right (logand u u4) 56)) in (* 0xFF00000000000000 *)
    b0,b1,b2,b3,b4,b5,b6,b7
;;

let to_bytes_native u : char * char * char * char * char * char * char * char =
  let u1 = Uint64.mul (Uint64.of_string "4278190080") (Uint64.of_string "255") in (* 0xFF00000000 *)
  let u2 = Uint64.mul (Uint64.of_string "4278190080") (Uint64.of_string "65280") in (* 0xFF0000000000 *)
  let u3 = Uint64.mul (Uint64.of_string "4278190080") (Uint64.of_string "16711680") in (* 0xFF000000000000 *)
  let u4 = Uint64.mul (Uint64.of_string "4278190080") (Uint64.of_string "4278190080") in (* 0xFF00000000000000 *)
  let b0 = Char.chr (Uint64.to_int (Uint64.logand u (Uint64.of_string "255"))) in (* 0xFF *)
  let b1 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u (Uint64.of_string "65280")) 8)) in (* 0xFF00 *)
  let b2 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u (Uint64.of_string "16711680")) 16)) in (* 0xFF0000 *)
  let b3 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u (Uint64.of_string "4278190080")) 24)) in (* 0xFF000000 *)
  let b4 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u u1) 32)) in (* 0xFF00000000 *)
  let b5 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u u2) 40)) in (* 0xFF0000000000 *)
  let b6 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u u3) 48)) in (* 0xFF000000000000 *)
  let b7 = Char.chr (Uint64.to_int (Uint64.shift_right (Uint64.logand u u4) 56)) in (* 0xFF00000000000000 *)
    b0,b1,b2,b3,b4,b5,b6,b7
;;
