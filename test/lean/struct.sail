default Order dec

$include <prelude.sail>

struct My_struct = {
  field1 : int,
  field2 : bit,
}

val struct_field2 : My_struct -> bit
function struct_field2(s) = {
  s.field2
}

val struct_update_field2 : (My_struct, bit) -> My_struct
function struct_update_field2(s, b) = {
  { s with field2 = b }
}

val struct_update_both_fields : (My_struct, int, bit) -> My_struct
function struct_update_both_fields(s, i, b) = {
  { s with field1 = i, field2 = b }
}

val mk_struct : (int, bit) -> My_struct
function mk_struct(i, b) = {
  struct { 
    field1 = i,
    field2 = b
  }
}

val undef_struct : bit -> My_struct
function undef_struct (x) = {
  (undefined_My_struct(): My_struct)
}

struct Mem_write_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type,
                         'arch_ak : Type), 'n > 0 & 'vasize >= 0 = {
  va : option(bits('vasize)),
  pa : 'pa,
  translation : 'ts,
  size : int('n),
  value : option(bits(8 * 'n)),
  tag : option(bool),
}
