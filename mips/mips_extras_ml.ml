open Sail_values
open Big_int_Z
open Printf

let big_int_to_hex i = Z.format "%x" i

module Mem = struct
  include Map.Make(struct
      type t = big_int
      let compare = compare_big_int
    end)
end

let cap_size_shift = ref 5;; (* caps every 2**5 = 32 bytes *)
let mem_pages = (ref Mem.empty : (Bytes.t Mem.t) ref);;
let tag_mem = (ref Mem.empty : (bool Mem.t) ref);;

let page_shift_bits = 20 (* 1M page *)
let page_size_bytes = 1 lsl page_shift_bits;; 


let page_no_of_addr a = shift_right_big_int a page_shift_bits;;
let bottom_addr_of_page p = shift_left_big_int p page_shift_bits
let top_addr_of_page p = shift_left_big_int (succ_big_int p) page_shift_bits
let get_page p =
  try
    Mem.find p !mem_pages
  with Not_found -> 
    let new_page = Bytes.create page_size_bytes in
    mem_pages := Mem.add p new_page !mem_pages;
    new_page
  
let rec add_mem_bytes addr buf off len =
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = int_of_big_int (sub_big_int addr page_bot) in
  let page = get_page page_no in
  let bytes_left_in_page = sub_big_int page_top addr in
  let to_copy = min_int (int_of_big_int bytes_left_in_page) len in
  Bytes.blit buf off page page_off to_copy;
  if (to_copy < len) then
    add_mem_bytes page_top buf (off + to_copy) (len - to_copy)

let rec read_mem_bytes addr len = 
  let page_no = page_no_of_addr addr in
  let page_bot = bottom_addr_of_page page_no in
  let page_top = top_addr_of_page page_no in
  let page_off = int_of_big_int (sub_big_int addr page_bot) in
  let page = get_page page_no in
  let bytes_left_in_page = sub_big_int page_top addr in
  let to_get = min_int (int_of_big_int bytes_left_in_page) len in
  let bytes = Bytes.sub page page_off to_get in
  if to_get >= len then
    bytes
  else
    Bytes.cat bytes (read_mem_bytes page_top (len - to_get))

let _MEMea (addr, size) = ()
let _MEMea_conditional = _MEMea
let _MEMea_tag  = _MEMea
let _MEMea_tag_conditional = _MEMea

let _MEMval (addr, size, data) =
  (* assumes data is decreasing vector to be stored in little-endian byte order in mem *)
  let s = int_of_big_int size in
  let a = unsigned_big(addr) in
  let buf = Bytes.create s in
  for i = 0 to (s - 1) do
    let bit_idx = i * 8 in
    let byte = unsigned_int(slice_raw (data, big_int_of_int bit_idx, big_int_of_int (bit_idx + 7))) in
    Bytes.set buf (s-1-i) (char_of_int byte);
  done;
  if !trace_writes then
    tracef "MEM[%s] <- %s\n" (big_int_to_hex a) (string_of_value data);
  add_mem_bytes a buf 0 s

let _MEMval_tag (addr, size, tag, data) =
  let addr_bi = (unsigned_big(addr)) in
  begin
    _MEMval (addr, size, data);
    tag_mem := Mem.add (shift_right_big_int addr_bi !cap_size_shift) (to_bool tag) !tag_mem;
  end

  
let _MEMval_conditional (addr, size, data) =
    let _ = _MEMval (addr, size, data) in
    Vone

let _MEMval_tag_conditional (addr, size, tag, data) =
    let _ = _MEMval_tag (addr, size, tag, data) in
    Vone

let _MEMr (addr, size) = begin
  let s = int_of_big_int size in
  let a = unsigned_big(addr) in
  let bytes = read_mem_bytes a s in
  let ret = ref (to_vec_dec_int (0, 0)) in
  for i = 0 to (s - 1) do
    let byte = Bytes.get bytes i in
    let byte_vec = to_vec_dec_int (8, int_of_char byte) in
    ret := vector_concat byte_vec (!ret);
    (*printf "MEM [%s] -> %x %s %s\n" (big_int_to_hex byte_addr) byte (string_of_value byte_vec) (string_of_value !ret);*)
  done;
  ret := set_start_to_length (!ret);
  !ret;
end
let _MEMr_reserve = _MEMr

let _MEMr_tag (addr, size) =
  let data = _MEMr(addr, size) in
  let addr_bi = unsigned_big(addr) in 
  let tag = try
      Mem.find (shift_right_big_int addr_bi !cap_size_shift) !tag_mem 
    with Not_found -> false in
  (bool_to_bit tag, data)

let _MEMr_tag_reserve = _MEMr_tag

let _MEM_sync _ = ()
