default Order dec

$include <prelude.sail>

struct MyStruct('n), 'n in {32, 64} = {
  field: bits('n)
}

type MyStruct32 = MyStruct(32)
type MyStruct64 = MyStruct(65)

let x : MyStruct64 = struct { field = 0b1 @ 0xFFFF_FFFF_FFFF_FFFF }
