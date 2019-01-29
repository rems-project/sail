module Big_int = Nat_big_num

type 'a return = { return : 'b . 'a -> 'b }
type 'za zoption = | ZNone of unit | ZSome of 'za;;

let zint_forwards i = string_of_int (Big_int.to_int i)

let opt_trace = ref false

let trace_depth = ref 0
let random = ref false

let sail_call (type t) (f : _ -> t) =
  let module M =
    struct exception Return of t end
  in
  let return = { return = (fun x -> raise (M.Return x)) } in
  try
    f return
  with M.Return x -> x

let trace str =
  if !opt_trace
  then
    begin
      if !trace_depth < 0 then trace_depth := 0 else ();
      prerr_endline (String.make (!trace_depth * 2) ' ' ^ str)
    end
  else ()

let trace_write name str =
  trace ("Write: " ^ name ^ " " ^ str)

let trace_read name str =
  trace ("Read: " ^ name ^ " " ^ str)

let sail_trace_call (type t) (name : string) (in_string : string) (string_of_out : t -> string) (f : _ -> t) =
  let module M =
    struct exception Return of t end
  in
  let return = { return = (fun x -> raise (M.Return x)) } in
  trace ("Call: " ^ name ^ " " ^ in_string);
  incr trace_depth;
  let result = try f return with M.Return x -> x in
  decr trace_depth;
  trace ("Return: " ^ string_of_out result);
  result

let trace_call str =
  trace str; incr trace_depth

type bit = B0 | B1

let eq_anything (a, b) = a = b

let eq_bit (a, b) = a = b

let and_bit = function
  | B1, B1 -> B1
  | _, _ -> B0

let or_bit = function
  | B0, B0 -> B0
  | _, _ -> B1

let xor_bit = function
  | B1, B0 -> B1
  | B0, B1 -> B1
  | _, _ -> B0

let and_vec (xs, ys) =
  assert (List.length xs = List.length ys);
  List.map2 (fun x y -> and_bit (x, y)) xs ys

let and_bool (b1, b2) = b1 && b2

let or_vec (xs, ys) =
  assert (List.length xs = List.length ys);
  List.map2 (fun x y -> or_bit (x, y)) xs ys

let or_bool (b1, b2) = b1 || b2

let xor_vec (xs, ys) =
  assert (List.length xs = List.length ys);
  List.map2 (fun x y -> xor_bit (x, y)) xs ys

let xor_bool (b1, b2) = (b1 || b2) && (b1 != b2)

let undefined_bit () =
  if !random
  then (if Random.bool () then B0 else B1)
  else B0

let undefined_bool () =
  if !random then Random.bool () else false

let rec undefined_vector (len, item) =
  if Big_int.equal len Big_int.zero
  then []
  else item :: undefined_vector (Big_int.sub len (Big_int.of_int 1), item)

let undefined_string () = ""

let undefined_unit () = ()

let undefined_int () =
  if !random then Big_int.of_int (Random.int 0xFFFF) else Big_int.zero

let undefined_nat () = Big_int.zero

let undefined_range (lo, hi) = lo

let internal_pick list =
  if !random
  then List.nth list (Random.int (List.length list))
  else List.nth list 0

let eq_int (n, m) = Big_int.equal n m

let eq_bool ((x : bool), (y : bool)) : bool = x = y

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
  let n = Big_int.to_int n in
  let m = Big_int.to_int m in
  List.rev (take (n - (m - 1)) (drop m (List.rev list)))

let slice (list, n, m) =
  let n = Big_int.to_int n in
  let m = Big_int.to_int m in
  List.rev (take m (drop n (List.rev list)))

let eq_list (xs, ys) = List.for_all2 (fun x y -> x = y) xs ys

let access (xs, n) = List.nth (List.rev xs) (Big_int.to_int n)

let append (xs, ys) = xs @ ys

let update (xs, n, x) =
  let n = (List.length xs - Big_int.to_int n) - 1 in
  take n xs @ [x] @ drop (n + 1) xs

let update_subrange (xs, n, m, ys) =
  let rec aux xs o = function
    | [] -> xs
    | (y :: ys) -> aux (update (xs, o, y)) (Big_int.sub o (Big_int.of_int 1)) ys
  in
  aux xs n ys

let vector_truncate (xs, n) = List.rev (take (Big_int.to_int n) (List.rev xs))

let vector_truncateLSB (xs, n) = take (Big_int.to_int n) xs

let length xs = Big_int.of_int (List.length xs)

let big_int_of_bit = function
  | B0 -> Big_int.zero
  | B1 -> (Big_int.of_int 1)

let uint xs =
  let uint_bit x (n, pos) =
    Big_int.add n (Big_int.mul (Big_int.pow_int_positive 2 pos) (big_int_of_bit x)), pos + 1
  in
  fst (List.fold_right uint_bit xs (Big_int.zero, 0))

let sint = function
  | [] -> Big_int.zero
  | [msb] -> Big_int.negate (big_int_of_bit msb)
  | msb :: xs ->
     let msb_pos = List.length xs in
     let complement =
       Big_int.negate (Big_int.mul (Big_int.pow_int_positive 2 msb_pos) (big_int_of_bit msb))
     in
     Big_int.add complement (uint xs)

let add_int (x, y) = Big_int.add x y
let sub_int (x, y) = Big_int.sub x y
let mult (x, y) = Big_int.mul x y
let quotient (x, y) = Big_int.div x y

(* Big_int does not provide divide with rounding towards zero so roll
   our own, assuming that division of positive integers rounds down *)
let quot_round_zero (x, y) = 
  let posX = Big_int.greater_equal x Big_int.zero in
  let posY = Big_int.greater_equal y Big_int.zero in
  let absX = Big_int.abs x in
  let absY = Big_int.abs y in
  let q = Big_int.div absX absY in
  if posX != posY then
    Big_int.negate q
  else
    q

(* The corresponding remainder function for above just respects the sign of x *)
let rem_round_zero (x, y) = 
  let posX = Big_int.greater_equal x Big_int.zero in
  let absX = Big_int.abs x in
  let absY = Big_int.abs y in
  let r = Big_int.modulus absX absY in
  if posX then
    r
  else
    Big_int.negate r

let modulus (x, y) = Big_int.modulus x y

let negate x = Big_int.negate x

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

let sub_bit_with_carry (x, y, carry) =
  match x, y, carry with
  | B0, B0, B0 -> B0, B0
  | B0, B1, B0 -> B0, B1
  | B1, B0, B0 -> B1, B0
  | B1, B1, B0 -> B0, B0
  | B0, B0, B1 -> B1, B0
  | B0, B1, B1 -> B0, B0
  | B1, B0, B1 -> B1, B1
  | B1, B1, B1 -> B1, B0

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
  if Big_int.less_equal n Big_int.zero
  then []
  else bits @ replicate_bits (bits, Big_int.sub n (Big_int.of_int 1))

let identity x = x



(* 
Returns list of n bits of integer m starting from offset o >= 0 (bits numbered from least significant). 
Uses twos-complement representation for m<0 and pads most significant bits in sign-extended way. 
Most significant bit is head of returned list.
 *)
let rec get_slice_int' (n, m, o) =
  if n <= 0 then
    []
  else
    let bit = if (Big_int.extract_num m (n + o - 1) 1) == Big_int.zero then B0 else B1 in
    bit :: get_slice_int' (n-1, m, o)

(* as above but taking Big_int for all arguments *)
let get_slice_int (n, m, o) = get_slice_int' (Big_int.to_int n, m, Big_int.to_int o)

(* as above but omitting offset, len is ocaml int *)
let to_bits' (len, n) = get_slice_int' (len, n, 0)

(* as above but taking big_int for length *)
let to_bits (len, n) = get_slice_int' (Big_int.to_int len, n, 0)

(* unsigned multiplication of two n bit lists producing a list of 2n bits *)
let mult_vec (x, y) =
  let xi = uint(x) in
  let yi = uint(y) in
  let len = List.length x in
  let prod = Big_int.mul xi yi in
  to_bits' (2*len, prod)

(* signed multiplication of two n bit lists producing a list of 2n bits. *)
let mults_vec (x, y) =
  let xi = sint(x) in
  let yi = sint(y) in
  let len = List.length x in
  let prod = Big_int.mul xi yi in
  to_bits' (2*len, prod)

let add_vec_int (v, n) =
  let n_bits = to_bits'(List.length v, n) in
  add_vec(v, n_bits)

let sub_vec (xs, ys) = add_vec (xs, add_vec_int (not_vec ys, (Big_int.of_int 1)))

let sub_vec_int (v, n) =
  let n_bits = to_bits'(List.length v, n) in
  sub_vec(v, n_bits)

let bin_char = function
  | '0' -> B0
  | '1' -> B1
  | _ -> failwith "Invalid binary character"

let hex_char = function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let list_of_string s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i-1) (s.[i] :: acc)
  in aux (String.length s - 1) []

let bits_of_string str =
  List.concat (List.map hex_char (list_of_string str))

let concat_str (str1, str2) = str1 ^ str2

let rec break n = function
  | [] -> []
  | (_ :: _ as xs) -> [take n xs] @ break n (drop n xs)

let string_of_bit = function
  | B0 -> "0"
  | B1 -> "1"

let char_of_bit = function
  | B0 -> '0'
  | B1 -> '1'

let int_of_bit = function
  | B0 -> 0
  | B1 -> 1

let bool_of_bit = function
  | B0 -> false
  | B1 -> true

let bit_of_bool = function
  | false -> B0
  | true -> B1

let bigint_of_bit b = Big_int.of_int (int_of_bit b)

let string_of_hex = function
  | [B0; B0; B0; B0] -> "0"
  | [B0; B0; B0; B1] -> "1"
  | [B0; B0; B1; B0] -> "2"
  | [B0; B0; B1; B1] -> "3"
  | [B0; B1; B0; B0] -> "4"
  | [B0; B1; B0; B1] -> "5"
  | [B0; B1; B1; B0] -> "6"
  | [B0; B1; B1; B1] -> "7"
  | [B1; B0; B0; B0] -> "8"
  | [B1; B0; B0; B1] -> "9"
  | [B1; B0; B1; B0] -> "A"
  | [B1; B0; B1; B1] -> "B"
  | [B1; B1; B0; B0] -> "C"
  | [B1; B1; B0; B1] -> "D"
  | [B1; B1; B1; B0] -> "E"
  | [B1; B1; B1; B1] -> "F"
  | _ -> failwith "Cannot convert binary sequence to hex"


let string_of_bits bits =
  if List.length bits mod 4 == 0
  then "0x" ^ String.concat "" (List.map string_of_hex (break 4 bits))
  else "0b" ^ String.concat "" (List.map string_of_bit bits)

let decimal_string_of_bits bits =
  let place_values =
    List.mapi
      (fun i b -> (Big_int.mul (bigint_of_bit b) (Big_int.pow_int_positive 2 i)))
      (List.rev bits)
  in
  let sum = List.fold_left Big_int.add Big_int.zero place_values in
  Big_int.to_string sum

let hex_slice (str, n, m) =
  let bits = List.concat (List.map hex_char (list_of_string (String.sub str 2 (String.length str - 2)))) in
  let padding = replicate_bits([B0], n) in
  let bits = padding @ bits in
  let slice = List.rev (take (Big_int.to_int n) (drop (Big_int.to_int m) (List.rev bits))) in
  slice

let putchar n =
  print_char (char_of_int (Big_int.to_int n));
  flush stdout

let rec bits_of_int bit n =
  if bit <> 0
  then
    begin
      if n / bit > 0
      then B1 :: bits_of_int (bit / 2) (n - bit)
      else B0 :: bits_of_int (bit / 2) n
    end
  else []

let rec bits_of_big_int pow n =
  if pow < 1 then []
  else begin
      let bit = (Big_int.pow_int_positive 2 (pow - 1)) in
      if Big_int.greater (Big_int.div n bit) Big_int.zero then
        B1 :: bits_of_big_int (pow - 1) (Big_int.sub n bit)
      else
        B0 :: bits_of_big_int (pow - 1) n
    end

let byte_of_int n = bits_of_int 128 n

module Mem = struct
  include Map.Make(struct
      type t = Big_int.num
      let compare = Big_int.compare
    end)
end

let mem_pages = (ref Mem.empty : (Bytes.t Mem.t) ref);;

let page_shift_bits = 20 (* 1M page *)
let page_size_bytes = 1 lsl page_shift_bits;; 

let page_no_of_addr a = Big_int.shift_right a page_shift_bits
let bottom_addr_of_page p = Big_int.shift_left p page_shift_bits
let top_addr_of_page p = Big_int.shift_left (Big_int.succ p) page_shift_bits
let get_mem_page p =
  try
    Mem.find p !mem_pages
  with Not_found -> 
    let new_page = Bytes.make page_size_bytes '\000' in
    mem_pages := Mem.add p new_page !mem_pages;
    new_page

let rec add_mem_bytes addr buf off len =
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = Big_int.to_int (Big_int.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Big_int.sub page_top addr in
  let to_copy = min (Big_int.to_int bytes_left_in_page) len in
  Bytes.blit buf off page page_off to_copy;
  if (to_copy < len) then
    add_mem_bytes page_top buf (off + to_copy) (len - to_copy)

let rec read_mem_bytes addr len = 
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = Big_int.to_int (Big_int.sub addr page_bot) in
  let page = get_mem_page page_no in
  let bytes_left_in_page = Big_int.sub page_top addr in
  let to_get = min (Big_int.to_int bytes_left_in_page) len in
  let bytes = Bytes.sub page page_off to_get in
  if to_get >= len then
    bytes
  else
    Bytes.cat bytes (read_mem_bytes page_top (len - to_get))

let write_ram' (data_size, addr, data) =
  let len   = Big_int.to_int data_size in
  let bytes = Bytes.create len in begin
    List.iteri (fun i byte -> Bytes.set bytes (len - i - 1) (char_of_int (Big_int.to_int (uint byte)))) (break 8 data);
    add_mem_bytes addr bytes 0 len
  end

let write_ram (addr_size, data_size, hex_ram, addr, data) =
  write_ram' (data_size, uint addr, data); true

let wram addr byte =
  let bytes = Bytes.make 1 (char_of_int byte) in
  add_mem_bytes addr bytes 0 1

let read_ram (addr_size, data_size, hex_ram, addr) =
  let addr = uint addr in
  let bytes = read_mem_bytes addr (Big_int.to_int data_size) in
  let vector = ref [] in
  Bytes.iter (fun byte -> vector := (byte_of_int (int_of_char byte)) @ !vector) bytes;
  !vector

let fast_read_ram (data_size, addr) =
  let addr = uint addr in
  let bytes = read_mem_bytes addr (Big_int.to_int data_size) in
  let vector = ref [] in
  Bytes.iter (fun byte -> vector := (byte_of_int (int_of_char byte)) @ !vector) bytes;
  !vector

let tag_ram = (ref Mem.empty : (bool Mem.t) ref);;
  
let write_tag_bool (addr, tag) =
  let addri = uint addr in
  tag_ram := Mem.add addri tag !tag_ram

let read_tag_bool addr =
  let addri = uint addr in
  try Mem.find addri !tag_ram with Not_found -> false

let rec reverse_endianness bits =
  if List.length bits <= 8 then bits else
  reverse_endianness (drop 8 bits) @ (take 8 bits)

(* FIXME: Casts can't be externed *)
let zcast_unit_vec x = [x]

let shl_int (n, m) = Big_int.shift_left n (Big_int.to_int m)
let shr_int (n, m) = Big_int.shift_right n (Big_int.to_int m)
let lor_int (n, m) = Big_int.bitwise_or n m
let land_int (n, m) = Big_int.bitwise_and n m
let lxor_int (n, m) = Big_int.bitwise_xor n m


let debug (str1, n, str2, v) = prerr_endline (str1 ^ Big_int.to_string n ^ str2 ^ string_of_bits v)

let eq_string (str1, str2) = String.compare str1 str2 == 0

let string_startswith (str1, str2) = String.length str1 >= String.length str2 && String.compare (String.sub str1 0 (String.length str2)) str2 == 0

let string_drop (str, n) = if (Big_int.less_equal (Big_int.of_int (String.length str)) n) then "" else let n = Big_int.to_int n in String.sub str n (String.length str - n)

let string_take (str, n) =
  let n = Big_int.to_int n in
  if String.length str <= n then
    str
  else
    String.sub str 0 n

let string_length str = Big_int.of_int (String.length str)

let string_append (s1, s2) = s1 ^ s2

let int_of_string_opt s =
  try
    Some (Big_int.of_string s)
  with
  | Invalid_argument _ -> None

(* highly inefficient recursive implementation *)
let rec maybe_int_of_prefix = function
  | "" -> ZNone ()
  | str ->
     let len = String.length str in
     match int_of_string_opt str with
     | Some n -> ZSome (n, Big_int.of_int len)
     | None -> maybe_int_of_prefix (String.sub str 0 (len - 1))

let maybe_int_of_string str =
  match int_of_string_opt str with
  | None -> ZNone ()
  | Some n -> ZSome n

let lt_int (x, y) = Big_int.less x y

let set_slice (out_len, slice_len, out, n, slice) =
  let out = update_subrange(out, Big_int.add n (Big_int.of_int (List.length slice - 1)), n, slice) in
  assert (List.length out = Big_int.to_int out_len);
  out

let set_slice_int (_, _, _, _) = assert false

let eq_real (x, y) = Rational.equal x y
let lt_real (x, y) = Rational.lt x y
let gt_real (x, y) = Rational.gt x y
let lteq_real (x, y) = Rational.leq x y
let gteq_real (x, y) = Rational.geq x y
let to_real x = Rational.of_int (Big_int.to_int x) (* FIXME *)
let negate_real x = Rational.neg x

let string_of_real x =
  if Big_int.equal (Rational.den x) (Big_int.of_int 1) then
    Big_int.to_string (Rational.num x)
  else
    Big_int.to_string (Rational.num x) ^ "/" ^ Big_int.to_string (Rational.den x)

let print_real (str, r) = print_endline (str ^ string_of_real r)
let prerr_real (str, r) = prerr_endline (str ^ string_of_real r)

let round_down x = Rational.floor x
let round_up x = Rational.ceiling x
let quotient_real (x, y) = Rational.div x y
let div_real (x, y) = Rational.div x y
let mult_real (x, y) = Rational.mul x y
let real_power (x, y) = failwith "real_power"
let int_power (x, y) = Big_int.pow_int x (Big_int.to_int y)
let add_real (x, y) = Rational.add x y
let sub_real (x, y) = Rational.sub x y

let abs_real x = Rational.abs x

let sqrt_real x =
  let precision = 30 in
  let s = Big_int.sqrt (Rational.num x) in
  if Big_int.equal (Rational.den x) (Big_int.of_int 1) && Big_int.equal (Big_int.mul s s) (Rational.num x) then
    to_real s
  else
    let p = ref (to_real (Big_int.sqrt (Big_int.div (Rational.num x) (Rational.den x)))) in
    let n = ref (Rational.of_int 0) in
    let convergence = ref (Rational.div (Rational.of_int 1) (Rational.of_big_int (Big_int.pow_int_positive 10 precision))) in
    let quit_loop = ref false in
    while not !quit_loop do
      n := Rational.div (Rational.add !p (Rational.div x !p)) (Rational.of_int 2);

      if Rational.lt (Rational.abs (Rational.sub !p !n)) !convergence then
        quit_loop := true
      else
        p := !n
    done;
    !n

let random_real () = Rational.div (Rational.of_int (Random.bits ())) (Rational.of_int (Random.bits()))

let lt (x, y) = Big_int.less x y
let gt (x, y) = Big_int.greater x y
let lteq (x, y) = Big_int.less_equal x y
let gteq (x, y) = Big_int.greater_equal x y

let pow2 x = Big_int.pow_int (Big_int.of_int 2) (Big_int.to_int x)

let max_int (x, y) = Big_int.max x y
let min_int (x, y) = Big_int.min x y
let abs_int x = Big_int.abs x

let string_of_int x = Big_int.to_string x

let undefined_real () = Rational.of_int 0

let rec pow x = function
  | 0 -> 1
  | n -> x * pow x (n - 1)

let real_of_string str =
  match Util.split_on_char '.' str with
  | [whole; frac] ->
     let whole = Rational.of_int (int_of_string whole) in
     let frac = Rational.div (Rational.of_int (int_of_string frac)) (Rational.of_int (pow 10 (String.length frac)))  in
     Rational.add whole frac
  | [whole] -> Rational.of_int (int_of_string str)
  | _ -> failwith "invalid real literal"

let print str = Pervasives.print_string str

let prerr str = Pervasives.prerr_string str

let print_int (str, x) =
  print_endline (str ^ Big_int.to_string x)

let prerr_int (str, x) =
  prerr_endline (str ^ Big_int.to_string x)

let print_bits (str, xs) =
  print_endline (str ^ string_of_bits xs)

let prerr_bits (str, xs) =
  prerr_endline (str ^ string_of_bits xs)

let print_string(str, msg) =
  print_endline (str ^ msg)

let prerr_string(str, msg) =
  prerr_endline (str ^ msg)

let reg_deref r = !r

let string_of_zbit = function
  | B0 -> "0"
  | B1 -> "1"
let string_of_znat n = Big_int.to_string n
let string_of_zint n = Big_int.to_string n
let string_of_zunit () = "()"
let string_of_zbool = function
  | true -> "true"
  | false -> "false"
let string_of_zreal r = "REAL"
let string_of_zstring str = "\"" ^ String.escaped str ^ "\""

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let skip () = ()

let memea (_, _) = ()

let zero_extend (vec, n) =
  let m = Big_int.to_int n in
  if m <= List.length vec
  then take m vec
  else replicate_bits ([B0], Big_int.of_int (m - List.length vec)) @ vec

let sign_extend (vec, n) =
  let m = Big_int.to_int n in
  match vec with
  | B0 :: _ as vec -> replicate_bits ([B0], Big_int.of_int (m - List.length vec)) @ vec
  | [] -> replicate_bits ([B0], Big_int.of_int (m - List.length vec)) @ vec
  | B1 :: _ as vec -> replicate_bits ([B1], Big_int.of_int (m - List.length vec)) @ vec

let zeros n = replicate_bits ([B0], n)

let shift_bits_right_arith (x, y) =
  let ybi = uint(y) in
  let msbs = replicate_bits (take 1 x, ybi) in
  let rbits = msbs @ x in
  take (List.length x) rbits

let shiftr (x, y) =
  let zeros = zeros y in
  let rbits = zeros @ x in
  take (List.length x) rbits

let shift_bits_right (x, y) =
  shiftr (x, uint(y))

let shiftl (x, y) =
  let yi  = Big_int.to_int y in
  let zeros = zeros y in
  let rbits = x @ zeros in
  drop yi rbits

let shift_bits_left (x, y) =
  shiftl (x, uint(y))

let speculate_conditional_success () = true

(* Return nanoseconds since epoch. Truncates to ocaml int but will be OK for next 100 years or so... *)
let get_time_ns () = Big_int.of_int (int_of_float (1e9 *. Unix.gettimeofday ()))

(* Python:
f = """let hex_bits_{0}_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 {0}) then
       ZSome ((bits_of_big_int {0} n, len))
     else
       ZNone ()
"""

for i in list(range(1, 34)) + [48, 64]:
  print(f.format(i))

*)
let hex_bits_1_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 1) then
       ZSome ((bits_of_big_int 1 n, len))
     else
       ZNone ()

let hex_bits_2_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 2) then
       ZSome ((bits_of_big_int 2 n, len))
     else
       ZNone ()

let hex_bits_3_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 3) then
       ZSome ((bits_of_big_int 3 n, len))
     else
       ZNone ()

let hex_bits_4_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 4) then
       ZSome ((bits_of_big_int 4 n, len))
     else
       ZNone ()

let hex_bits_5_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 5) then
       ZSome ((bits_of_big_int 5 n, len))
     else
       ZNone ()

let hex_bits_6_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 6) then
       ZSome ((bits_of_big_int 6 n, len))
     else
       ZNone ()

let hex_bits_7_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 7) then
       ZSome ((bits_of_big_int 7 n, len))
     else
       ZNone ()

let hex_bits_8_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 8) then
       ZSome ((bits_of_big_int 8 n, len))
     else
       ZNone ()

let hex_bits_9_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 9) then
       ZSome ((bits_of_big_int 9 n, len))
     else
       ZNone ()

let hex_bits_10_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 10) then
       ZSome ((bits_of_big_int 10 n, len))
     else
       ZNone ()

let hex_bits_11_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 11) then
       ZSome ((bits_of_big_int 11 n, len))
     else
       ZNone ()

let hex_bits_12_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 12) then
       ZSome ((bits_of_big_int 12 n, len))
     else
       ZNone ()

let hex_bits_13_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 13) then
       ZSome ((bits_of_big_int 13 n, len))
     else
       ZNone ()

let hex_bits_14_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 14) then
       ZSome ((bits_of_big_int 14 n, len))
     else
       ZNone ()

let hex_bits_15_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 15) then
       ZSome ((bits_of_big_int 15 n, len))
     else
       ZNone ()

let hex_bits_16_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 16) then
       ZSome ((bits_of_big_int 16 n, len))
     else
       ZNone ()

let hex_bits_17_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 17) then
       ZSome ((bits_of_big_int 17 n, len))
     else
       ZNone ()

let hex_bits_18_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 18) then
       ZSome ((bits_of_big_int 18 n, len))
     else
       ZNone ()

let hex_bits_19_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 19) then
       ZSome ((bits_of_big_int 19 n, len))
     else
       ZNone ()

let hex_bits_20_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 20) then
       ZSome ((bits_of_big_int 20 n, len))
     else
       ZNone ()

let hex_bits_21_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 21) then
       ZSome ((bits_of_big_int 21 n, len))
     else
       ZNone ()

let hex_bits_22_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 22) then
       ZSome ((bits_of_big_int 22 n, len))
     else
       ZNone ()

let hex_bits_23_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 23) then
       ZSome ((bits_of_big_int 23 n, len))
     else
       ZNone ()

let hex_bits_24_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 24) then
       ZSome ((bits_of_big_int 24 n, len))
     else
       ZNone ()

let hex_bits_25_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 25) then
       ZSome ((bits_of_big_int 25 n, len))
     else
       ZNone ()

let hex_bits_26_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 26) then
       ZSome ((bits_of_big_int 26 n, len))
     else
       ZNone ()

let hex_bits_27_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 27) then
       ZSome ((bits_of_big_int 27 n, len))
     else
       ZNone ()

let hex_bits_28_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 28) then
       ZSome ((bits_of_big_int 28 n, len))
     else
       ZNone ()

let hex_bits_29_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 29) then
       ZSome ((bits_of_big_int 29 n, len))
     else
       ZNone ()

let hex_bits_30_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 30) then
       ZSome ((bits_of_big_int 30 n, len))
     else
       ZNone ()

let hex_bits_31_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 31) then
       ZSome ((bits_of_big_int 31 n, len))
     else
       ZNone ()

let hex_bits_32_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 32) then
       ZSome ((bits_of_big_int 32 n, len))
     else
       ZNone ()

let hex_bits_33_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 33) then
       ZSome ((bits_of_big_int 33 n, len))
     else
       ZNone ()

let hex_bits_48_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 48) then
       ZSome ((bits_of_big_int 48 n, len))
     else
       ZNone ()

let hex_bits_64_matches_prefix s =
  match maybe_int_of_prefix s with
  | ZNone () -> ZNone ()
  | ZSome (n, len) ->
     if Big_int.less_equal Big_int.zero n
        && Big_int.less n (Big_int.pow_int_positive 2 64) then
       ZSome ((bits_of_big_int 64 n, len))
     else
       ZNone ()


let string_of_bool = function
  | true -> "true"
  | false -> "false"

let dec_str x = Big_int.to_string x

let hex_str x = Big_int.to_string x

let trace_memory_write (_, _, _) = ()
let trace_memory_read (_, _, _) = ()

let sleep_request () = ()

let load_raw (paddr, file) =
  let i = ref 0 in
  let paddr = uint paddr in
  let in_chan = open_in file in
  try
    while true do
      let byte = input_char in_chan |> Char.code in
      wram (Big_int.add paddr (Big_int.of_int !i)) byte;
      incr i
    done
  with
  | End_of_file -> ()

(* XXX this could count cycles and exit after given limit *)
let cycle_count () = ()

(* TODO range, atom, register(?), int, nat, bool, real(!), list, string, itself(?) *)
let rand_zvector (g : 'generators) (size : int) (order : bool) (elem_gen : 'generators -> 'a) : 'a list =
  Util.list_init size (fun _ -> elem_gen g)

let rand_zbit (g : 'generators) : bit =
  bit_of_bool (Random.bool())

let rand_zbool (g : 'generators) : bool =
  Random.bool()

let rand_zunit (g : 'generators) : unit = ()

let rand_choice l =
  let n = List.length l in
  List.nth l (Random.int n)
