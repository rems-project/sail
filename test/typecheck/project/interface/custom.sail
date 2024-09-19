$sail_internal

type bar = unit

outcome test : 'a -> unit
with 'a : Type = {
    val foo : 'a -> bar
}
