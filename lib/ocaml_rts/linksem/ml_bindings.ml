open Endianness
open Error

open Printf
open Unix

let string_of_unix_time (tm : Nat_big_num.num) =
  let num  = Nat_big_num.to_int64 tm in
  let tm   = Unix.gmtime (Int64.to_float num) in
  let day  = tm.tm_mday in
  let mon  = 1 + tm.tm_mon in
  let year = 1900 + tm.tm_year in
  let hour = tm.tm_hour in
  let min  = tm.tm_min in
  let sec  = tm.tm_sec in
    Printf.sprintf "%i-%i-%iT%02i:%02i:%02i" year mon day hour min sec

let hex_string_of_nat_pad2 i : string =
  Printf.sprintf "%02i" i
;;

let hex_string_of_big_int_pad6 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%06Lx" i0
;;

let hex_string_of_big_int_pad7 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%07Lx" i0
;;

let hex_string_of_big_int_pad2 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%02Lx" i0
;;

let hex_string_of_big_int_pad4 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%04Lx" i0
;;

let hex_string_of_big_int_pad5 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%05Lx" i0
;;

let hex_string_of_big_int_pad8 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%08Lx" i0
;;

let hex_string_of_big_int_pad16 i : string =
  let i0 = Nat_big_num.to_int64 i in
    Printf.sprintf "%016Lx" i0
;;

let hex_string_of_big_int_no_padding i : string =
  let i0 = Nat_big_num.to_int64 i in
    if Int64.compare i0 Int64.zero < 0 then
      let i0 = Int64.neg i0 in
        Printf.sprintf "-%Lx" i0
    else
      Printf.sprintf "%Lx" i0
;;

let bytes_of_int32 (i : Int32.t) = assert false
;;

let bytes_of_int64 (i : Int64.t) = assert false
;;

let int32_of_quad c1 c2 c3 c4 =
  let b1 = Int32.of_int (Char.code c1) in
  let b2 = Int32.shift_left (Int32.of_int (Char.code c2)) 8 in
  let b3 = Int32.shift_left (Int32.of_int (Char.code c3)) 16 in
  let b4 = Int32.shift_left (Int32.of_int (Char.code c4)) 24 in
    Int32.add b1 (Int32.add b2 (Int32.add b3 b4))
;;

let int64_of_oct c1 c2 c3 c4 c5 c6 c7 c8 =
  let b1 = Int64.of_int (Char.code c1) in
  let b2 = Int64.shift_left (Int64.of_int (Char.code c2)) 8 in
  let b3 = Int64.shift_left (Int64.of_int (Char.code c3)) 16 in
  let b4 = Int64.shift_left (Int64.of_int (Char.code c4)) 24 in
  let b5 = Int64.shift_left (Int64.of_int (Char.code c5)) 32 in
  let b6 = Int64.shift_left (Int64.of_int (Char.code c6)) 40 in
  let b7 = Int64.shift_left (Int64.of_int (Char.code c7)) 48 in
  let b8 = Int64.shift_left (Int64.of_int (Char.code c8)) 56 in
    Int64.add b1 (Int64.add b2 (Int64.add b3 (Int64.add b4
        (Int64.add b5 (Int64.add b6 (Int64.add b7 b8))))))
;;

let decimal_string_of_int64 e =
  let i = Int64.to_int e in
    string_of_int i
;;

let hex_string_of_int64 (e : Int64.t) : string =
  let i = Int64.to_int e in
    Printf.sprintf "0x%x" i
;;

let string_suffix index str =
  if (* index < 0 *) Nat_big_num.less index (Nat_big_num.of_int 0) ||
     (* index > length str *) (Nat_big_num.greater index (Nat_big_num.of_int (String.length str))) then
    None
  else
  	let idx = Nat_big_num.to_int index in
  		Some (String.sub str idx (String.length str - idx))
;;

let string_prefix index str =
  if (* index < 0 *) Nat_big_num.less index (Nat_big_num.of_int 0) ||
     (* index > length str *) (Nat_big_num.greater index (Nat_big_num.of_int (String.length str))) then
    None
  else
  	let idx = Nat_big_num.to_int index in
  		Some (String.sub str 0 idx)
;;

let string_index_of (c: char) (s : string) = try Some(Nat_big_num.of_int (String.index s c))
    with Not_found -> None
;;

let find_substring (sub: string) (s : string) = 
    try Some(Nat_big_num.of_int (Str.search_forward (Str.regexp_string sub) s 0))
    with Not_found -> None
;;

let rec list_index_big_int index xs =
  match xs with
    | []    -> None
    | x::xs ->
      if Nat_big_num.equal index (Nat_big_num.of_int 0) then
        Some x
      else
        list_index_big_int (Nat_big_num.sub index (Nat_big_num.of_int 1)) xs
;;

let argv_list = Array.to_list Sys.argv
;;

let nat_big_num_of_uint64 x = 
    (* Nat_big_num can only be made from signed integers at present. 
     * Workaround: make an int64, and if negative, add the high bit
     * in the big-num domain. *)
    let via_int64 = Uint64.to_int64 x
    in
    if Int64.compare via_int64 Int64.zero >= 0 then Nat_big_num.of_int64 via_int64
    else
        let two_to_63 = Uint64.shift_left (Uint64.of_int 1) 63 in
        let lower_by_2_to_63 = Uint64.sub x two_to_63 in
        (Nat_big_num.add 
            (Nat_big_num.of_int64 (Uint64.to_int64 lower_by_2_to_63))
            (Nat_big_num.shift_left (Nat_big_num.of_int 1) 63)
        )
