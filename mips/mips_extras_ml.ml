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

let mips_mem = (ref Mem.empty : (int Mem.t) ref);;
let tag_mem = (ref Mem.empty : (bool Mem.t) ref);;

let _MEMea (addr, size) = ()
let _MEMea_conditional = _MEMea
let _MEMea_tag  = _MEMea
let _MEMea_tag_conditional = _MEMea

let _MEMval (addr, size, data) =
  (* assumes data is decreasing vector to be stored in little-endian byte order in mem *)
  let s = int_of_big_int size in
  let a = unsigned_big(addr) in
  for i = 0 to (s - 1) do
    let bit_idx = i * 8 in
    let byte = unsigned_int(slice_raw (data, big_int_of_int bit_idx, big_int_of_int (bit_idx + 7))) in
    let byte_addr = add_int_big_int (s-1-i) a in
    begin
      (*printf "MEM [%s] <- %x\n" (big_int_to_hex byte_addr) byte;*)
      mips_mem := Mem.add byte_addr byte !mips_mem;
    end
  done

let _MEMval_tag (addr, size, data) =
  let tag = bit_vector_access_int data 0 in
  let data = vector_subrange_int data (8*(int_of_big_int size) + 7) 8 in 
  let addr_bi = (unsigned_big(addr)) in
  begin
    _MEMval (addr, size, data);
    tag_mem := Mem.add addr_bi (to_bool tag) !tag_mem;
  end

  
let _MEMval_conditional (addr, size, data) =
    let _ = _MEMval (addr, size, data) in
    Vone

let _MEMval_tag_conditional (addr, size, data) =
    let _ = _MEMval_tag (addr, size, data) in
    Vone

let _MEMr (addr, size) = begin
  let s = int_of_big_int size in
  let a = unsigned_big(addr) in
  let ret = ref (to_vec_dec_int (0, 0)) in
  for i = 0 to (s - 1) do
    let byte_addr = add_int_big_int i a in
    let byte_vec = 
      try
        let byte = Mem.find byte_addr !mips_mem in
        to_vec_dec_int (8, byte)
      with Not_found -> 
        to_vec_dec_int (8, 0) in (* XXX return 0 for uninitialised memory. Optionally return undef instead. *)
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
      Mem.find addr_bi !tag_mem 
    with Not_found -> false in
  begin
    set_start_to_length (vector_concat data (to_vec_dec_int (8, if tag then 1 else 0)))
  end

let _MEMr_tag_reserve = _MEMr_tag

let _TAGw (addr, tag) = 
  begin
    tag_mem := Mem.add (unsigned_big addr) (to_bool (bit_vector_access_int tag 0)) !tag_mem
  end

let _MEM_sync _ = ()
