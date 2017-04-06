open Sail_values
open Big_int_Z
open Printf

let big_int_to_hex i = Uint64.to_string_hex (Uint64.of_string (string_of_big_int i))

module Mem = struct
  include Map.Make(struct
      type t = big_int
      let compare = compare_big_int
    end)
end

let mips_mem = (ref Mem.empty : (int Mem.t) ref);;

let _MEMea (addr, size) = ()
let _MEMea_conditional = _MEMea

let _MEMval (addr, size, data) =
  (* assumes data is decreasing vector to be stored in big-endian byte order in mem *)
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
  
let _MEMval_conditional (addr, size, data) =
    let _ = _MEMval (addr, size, data) in
    Vone

let _MEMr (addr, size) = begin
  let s = int_of_big_int size in
  let a = unsigned_big(addr) in
  let ret = ref (to_vec_dec_int (0, 0)) in
  for i = 0 to (s - 1) do
    let byte_addr = add_int_big_int i a in
    let byte = Mem.find byte_addr !mips_mem in
    let byte_vec = to_vec_dec_int (8, byte) in
    ret := vector_concat byte_vec (!ret);
    (*printf "MEM [%s] -> %x %s %s\n" (big_int_to_hex byte_addr) byte (string_of_value byte_vec) (string_of_value !ret);*)
  done;
  ret := set_start_to_length (!ret);
  !ret;
end
let _MEMr_reserve = _MEMr

let _MEM_sync _ = ()
