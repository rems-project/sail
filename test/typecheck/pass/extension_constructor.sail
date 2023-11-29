$option -dmagic_hash

$project# A { } B { requires A } C { requires A }

// Module A
$start_module# A

union Foo = {
  Bar : unit,
  $[extension B] Baz : unit,
}

$end_module# A

// Module B
$start_module# B

val bravo : unit -> unit

function bravo() = {
  let _ = Baz();
}

$end_module# B

// Module C
$start_module# C

val charlie : Foo -> unit

function charlie(x) = {
  match x {
    Bar() => (),
    _ => (),
  }
}

$end_module# C
