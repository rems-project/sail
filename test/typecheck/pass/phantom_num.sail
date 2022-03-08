function __id forall 'n. (x: int('n)) -> int('n) = x

overload __size = {__id}

val gt_int = pure {ocaml: "gt", lem: "gt"}: (int, int) -> bool

overload operator > = {gt_int}

register z : int

val test : forall ('n : Int). (implicit('n), unit) -> unit effect {wreg}

function test(n, _) = if 'n > 3 then z = 0 else z = 1
