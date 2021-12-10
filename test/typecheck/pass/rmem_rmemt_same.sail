default Order dec

$include <prelude.sail>

val test : unit -> unit effect {rmem, rmemt}

function test() = ()

val test2 : unit -> unit effect {rmem}

function test2() = test()

val test3 : unit -> unit effect {rmemt}

function test3() = test()

val test4 : unit -> unit effect {rmem}

function test4() = test3()
