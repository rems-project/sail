default Order dec

$include <prelude.sail>

enum Extension = { ExtA, ExtB }

val guarded : Extension -> bool
function guarded (ExtA if true) = true
and guarded ExtB = false

val wildcard : Extension -> bool
function wildcard _ = true

val collision : Extension -> bool
function collision ExtA = true
and collision ExtB = false

function collision_ExtA() -> bool = true

val external_function = pure { c: "external_function", cpp: "external_function" } : Extension -> bool
function external_function ExtA = true
and external_function ExtB = false

val polymorphic : forall ('n : Int). Extension -> bool
function polymorphic ExtA = true
and polymorphic ExtB = false

register register_collision_ExtA : bool = true
val register_collision : Extension -> bool
function register_collision ExtA = true
and register_collision ExtB = false

function main() -> unit = ()
