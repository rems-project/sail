default Order dec

$include <prelude.sail>

outcome foo : vector('m, 'n) -> unit with 'n, 'm

outcome bar : vector('n, 'm) -> unit with 'n, 'm
