default Order inc

union option ('a : Type) = {None : unit, Some : 'a}

union Test = {A : unit, B : unit, C : unit}

function test () -> option(Test) = Some(C())
