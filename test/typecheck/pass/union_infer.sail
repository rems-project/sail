default Order inc

union option ('a : Type) = {None, Some : 'a}

union Test = {A, B, C}

function test () -> option(Test) = Some(C)
