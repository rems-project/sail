default Order dec
$include <prelude.sail>

/* This was written to manually inspect that "let n = size_itself_int n in" gets
   added in the right places, but it's also worth running in case that gets
   broken. */

val needs_size_in_guard : forall 'n. int('n) -> unit

function needs_size_in_guard(n if n > 8) = {
  let x : bits('n) = replicate_bits(0b0,n);
  ()
}
and needs_size_in_guard(n) = {
  let x : bits('n) = replicate_bits(0b1,n);
  ()
}

val no_size_in_guard : forall 'n. (int('n), int) -> unit

function no_size_in_guard((n,m) if m > 8) = {
  let x : bits('n) = replicate_bits(0b0,n);
  ()
}
and no_size_in_guard(n,m) = {
  let x : bits('n) = replicate_bits(0b1,n);
  ()
}

val shadowed : forall 'n. int('n) -> unit

function shadowed(n) = {
  let n = 8;
  let x : bits(8) = replicate_bits(0b0,n);
  ()
}

val willsplit : bool -> unit

function willsplit(x) = {
  let 'n : int = if x then 8 else 16;
  needs_size_in_guard(n);
  no_size_in_guard(n,n);
  shadowed(n);
}

val execute : forall 'datasize. int('datasize) -> unit

function execute(datasize) = {
  let x : bits('datasize) = replicate_bits(0b1, datasize);
  ()
}

val test_execute : unit -> unit

function test_execute() = {
  let exp = 4;
  let 'datasize = shl_int(1, exp);
  execute(datasize)
}

val transitive_itself : forall 'n. int('n) -> unit

function transitive_itself(n) = {
  needs_size_in_guard(n);
  ()
}

val transitive_split : bool -> unit

function transitive_split(x) = {
  let n = if x then 8 else 16;
  transitive_itself(n);
}

val run : unit -> unit

function run () = {
  assert(true); /* To force us into the monad */
  test_execute();
  willsplit(true);
  willsplit(false);
  transitive_itself(16);
  transitive_split(true);
  transitive_split(false);
}
