open Ast
open Bit
open Datatypes
open List0
open ListDef

(** val same_bits : bit list -> bit list -> bool **)

let same_bits bs vs =
  fst
    (fold_left (fun match_info b ->
      let (y, y0) = match_info in
      if y
      then (match y0 with
            | [] -> (false, [])
            | y1 :: vs0 ->
              (match y1 with
               | B0 -> (match b with
                        | B0 -> (true, vs0)
                        | B1 -> (false, []))
               | B1 -> (match b with
                        | B0 -> (false, [])
                        | B1 -> (true, vs0))))
      else (false, [])) bs (true, vs))

(** val of_hex_digit : hex_digit -> bit list **)

let of_hex_digit = function
| Hex_0 -> B0 :: (B0 :: (B0 :: (B0 :: [])))
| Hex_1 -> B0 :: (B0 :: (B0 :: (B1 :: [])))
| Hex_2 -> B0 :: (B0 :: (B1 :: (B0 :: [])))
| Hex_3 -> B0 :: (B0 :: (B1 :: (B1 :: [])))
| Hex_4 -> B0 :: (B1 :: (B0 :: (B0 :: [])))
| Hex_5 -> B0 :: (B1 :: (B0 :: (B1 :: [])))
| Hex_6 -> B0 :: (B1 :: (B1 :: (B0 :: [])))
| Hex_7 -> B0 :: (B1 :: (B1 :: (B1 :: [])))
| Hex_8 -> B1 :: (B0 :: (B0 :: (B0 :: [])))
| Hex_9 -> B1 :: (B0 :: (B0 :: (B1 :: [])))
| Hex_A -> B1 :: (B0 :: (B1 :: (B0 :: [])))
| Hex_B -> B1 :: (B0 :: (B1 :: (B1 :: [])))
| Hex_C -> B1 :: (B1 :: (B0 :: (B0 :: [])))
| Hex_D -> B1 :: (B1 :: (B0 :: (B1 :: [])))
| Hex_E -> B1 :: (B1 :: (B1 :: (B0 :: [])))
| Hex_F -> B1 :: (B1 :: (B1 :: (B1 :: [])))

(** val hex_digit_of_nibble : bit -> bit -> bit -> bit -> hex_digit **)

let hex_digit_of_nibble b1 b2 b3 b4 =
  let p = ((b1, b2), b3) in
  let (p0, b0) = p in
  let (b5, b6) = p0 in
  (match b5 with
   | B0 ->
     (match b6 with
      | B0 ->
        (match b0 with
         | B0 -> (match b4 with
                  | B0 -> Hex_0
                  | B1 -> Hex_1)
         | B1 -> (match b4 with
                  | B0 -> Hex_2
                  | B1 -> Hex_3))
      | B1 ->
        (match b0 with
         | B0 -> (match b4 with
                  | B0 -> Hex_4
                  | B1 -> Hex_5)
         | B1 -> (match b4 with
                  | B0 -> Hex_6
                  | B1 -> Hex_7)))
   | B1 ->
     (match b6 with
      | B0 ->
        (match b0 with
         | B0 -> (match b4 with
                  | B0 -> Hex_8
                  | B1 -> Hex_9)
         | B1 -> (match b4 with
                  | B0 -> Hex_A
                  | B1 -> Hex_B))
      | B1 ->
        (match b0 with
         | B0 -> (match b4 with
                  | B0 -> Hex_C
                  | B1 -> Hex_D)
         | B1 -> (match b4 with
                  | B0 -> Hex_E
                  | B1 -> Hex_F))))

(** val to_hex_digits : bit list -> hex_digit list option **)

let rec to_hex_digits = function
| [] -> Some []
| b1 :: l ->
  (match l with
   | [] -> None
   | b2 :: l0 ->
     (match l0 with
      | [] -> None
      | b3 :: l1 ->
        (match l1 with
         | [] -> None
         | b4 :: rest ->
           let digit = hex_digit_of_nibble b1 b2 b3 b4 in
           (match to_hex_digits rest with
            | Some digits -> Some (digit :: digits)
            | None -> None))))

(** val non_empty_to_list : 'a1 non_empty -> 'a1 list **)

let non_empty_to_list = function
| Non_empty (y, ys) -> y :: ys

(** val of_hex_lit : hex_digit non_empty list -> bit list **)

let of_hex_lit hex =
  let digits = concat (map non_empty_to_list hex) in
  concat (map of_hex_digit digits)

(** val of_bin_lit : bin_digit non_empty list -> bit list **)

let of_bin_lit bin =
  let digits = concat (map non_empty_to_list bin) in
  map (fun b -> match b with
                | Bin_0 -> B0
                | Bin_1 -> B1) digits

(** val to_gvector : value -> value **)

let to_gvector v = match v with
| V_bitvector bs -> V_vector (map (fun b -> V_bitvector (b :: [])) bs)
| _ -> v
