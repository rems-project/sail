default Order dec

$include <prelude.sail>

val branch : range(0, 63) -> range(0, 63)

function branch x = if x < 32 then x + 2 else x - 2
