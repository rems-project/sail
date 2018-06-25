$ifndef _TRACE
$define _TRACE

val enable_tracing = {
  c: "enable_tracing"
} : unit -> unit

function enable_tracing() = ()

val disable_tracing = {
  c: "disable_tracing"
} : unit -> unit

function disable_tracing() = ()

val is_tracing = {
  c: "is_tracing"
} : unit -> bool

function is_tracing() = false

$endif
