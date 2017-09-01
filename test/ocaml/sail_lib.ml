open Big_int

type 'a return = { return : 'b . 'a -> 'b }

let with_return (type t) (f : _ -> t) =
  let module M =
    struct exception Return of t end
  in
  let return = { return = (fun x -> raise (M.Return x)); } in
  try f return with M.Return x -> x

type bit = B0 | B1

let and_bit = function
  | B1, B1 -> B1
  | _, _ -> B0

let or_bit = function
  | B0, B0 -> B0
  | _, _ -> B1

let and_vec (xs, ys) =
  assert (List.length xs = List.length ys);
  List.map2 (fun x y -> and_bit (x, y)) xs ys

let and_bool (b1, b2) = b1 && b2

let or_vec (xs, ys) =
  assert (List.length xs = List.length ys);
  List.map2 (fun x y -> or_bit (x, y)) xs ys

let or_bool (b1, b2) = b1 || b2

let undefined_bit () =
  if Random.bool () then B0 else B1

let undefined_bool () = Random.bool ()

let rec undefined_vector (start_index, len, item) =
  if eq_big_int len zero_big_int
  then []
  else item :: undefined_vector (start_index, sub_big_int len unit_big_int, item)

let undefined_string () = ""

let undefined_unit () = ()

let undefined_int () =
  big_int_of_int (Random.int 0xFFFF)

let internal_pick list =
  List.nth list (Random.int (List.length list))

let eq_int (n, m) = eq_big_int n m

let eq_string (str1, str2) = String.compare str1 str2 = 0

let concat_string (str1, str2) = str1 ^ str2

let rec drop n xs =
  match n, xs with
  | 0, xs -> xs
  | n, [] -> []
  | n, (x :: xs) -> drop (n -1) xs

let rec take n xs =
  match n, xs with
  | 0, xs -> []
  | n, (x :: xs) -> x :: take (n - 1) xs
  | n, [] -> []

let subrange (list, n, m) =
  let n = int_of_big_int n in
  let m = int_of_big_int m in
  List.rev (take (n - (m - 1)) (drop m (List.rev list)))

let eq_list (xs, ys) = List.for_all2 (fun x y -> x == y) xs ys

let access (xs, n) = List.nth (List.rev xs) (int_of_big_int n)

let append (xs, ys) = xs @ ys

let update (xs, n, x) =
  let n = int_of_big_int n in
  take n xs @ [x] @ drop (n + 1) xs

let update_subrange (xs, n, m, ys) =
  let n = int_of_big_int n in
  let m = int_of_big_int m in
  assert false

let length xs = big_int_of_int (List.length xs)

let big_int_of_bit = function
  | B0 -> zero_big_int
  | B1 -> unit_big_int

let uint xs =
  let uint_bit x (n, pos) =
    add_big_int n (mult_big_int (power_int_positive_int 2 pos) (big_int_of_bit x)), pos + 1
  in
  fst (List.fold_right uint_bit xs (zero_big_int, 0))

let sint = function
  | [] -> zero_big_int
  | [msb] -> minus_big_int (big_int_of_bit msb)
  | msb :: xs ->
     let msb_pos = List.length xs in
     let complement =
       minus_big_int (mult_big_int (power_int_positive_int 2 msb_pos) (big_int_of_bit msb))
     in
     add_big_int complement (uint xs)

let add (x, y) = add_big_int x y
let sub (x, y) = sub_big_int x y
let mult (x, y) = mult_big_int x y
let quotient (x, y) = fst (quomod_big_int x y)
let modulus (x, y) = snd (quomod_big_int x y)

let add_bit_with_carry (x, y, carry) =
  match x, y, carry with
  | B0, B0, B0 -> B0, B0
  | B0, B1, B0 -> B1, B0
  | B1, B0, B0 -> B1, B0
  | B1, B1, B0 -> B0, B1
  | B0, B0, B1 -> B1, B0
  | B0, B1, B1 -> B0, B1
  | B1, B0, B1 -> B0, B1
  | B1, B1, B1 -> B1, B1

let not_bit = function
  | B0 -> B1
  | B1 -> B0

let not_vec xs = List.map not_bit xs

let add_vec_carry (xs, ys) =
  assert (List.length xs = List.length ys);
  let (carry, result) =
    List.fold_right2 (fun x y (c, result) -> let (z, c) = add_bit_with_carry (x, y, c) in (c, z :: result)) xs ys (B0, [])
  in
  carry, result

let add_vec (xs, ys) = snd (add_vec_carry (xs, ys))

let rec replicate_bits (bits, n) =
  if eq_big_int n zero_big_int
  then []
  else bits @ replicate_bits (bits, sub_big_int n unit_big_int)

let identity x = x

let get_slice_int (n, m, o) = assert false

let hex_slice (str, n, m) = assert false

let putchar n = print_endline (string_of_big_int n)

let write_ram (addr_size, data_size, hex_ram, addr, data) =
  assert false

let read_ram (addr_size, data_size, hex_ram, addr) =
  assert false

(* FIXME: Casts can't be externed *)
let zcast_unit_vec x = [x]

let shl_int (n, m) = assert false
let shr_int (n, m) = assert false
