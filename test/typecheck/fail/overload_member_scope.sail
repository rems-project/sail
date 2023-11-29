$option -dmagic_hash

// This test demonstrates that even though bar overloads foo, we
// cannot use bar to access foo in a module where it is not available

// While it might make some sense to permit this (essentially using an
// overload to re-export a function), it would break the property we want
// that allows us to cleanly remove optional modules if they overload
// identifiers.

$project# A { } B { requires A } C { requires B }

$start_module# A

val foo : unit -> unit

$end_module# A

$start_module# B

overload bar = {foo}

$end_module# B

$start_module# C

val baz : unit -> unit

function baz() = bar()

$end_module# C
