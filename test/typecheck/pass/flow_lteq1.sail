default Order dec

$include <prelude.sail>

function branch x : range(0, 63) -> range(0, 63) = if x <= 32 then x + 31 else x - 33
