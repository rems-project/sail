default Order dec
$include <prelude.sail>

outcome foo : unit -> unit
with 'a : Int
= {
  impl $[a] foo() = ()
}
