val gt_int = {ocaml: "gt", lem: "gt"}: (int, int) -> bool

overload operator > = {gt_int}

register z : int

val test : forall ('n : Int). unit -> unit effect {wreg}

function test () = if 'n > 3 then z = 0 else z = 1
