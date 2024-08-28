struct MyStruct = { f : bool }

let my_struct : MyStruct = struct { f = true }

$property
function prop() -> bool = my_struct.f
