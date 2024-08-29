$include <generic_equality.sail>

struct MyStruct = { f : range(0,1) }

let my_struct : MyStruct = struct { f = 0 }

$property
function prop() -> bool = my_struct.f == 0
