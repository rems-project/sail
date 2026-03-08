default Order dec

$include <prelude.sail>

infixr 5 ^^

overload operator ^^ = {concat_str}

union exception = {
    Error_internal_error : unit
}

val internal_error : forall ('a : Type). (string, int, string) -> 'a

function internal_error(file, line, s) = {
    assert (false, file ^^ ":" ^^ dec_str(line) ^^ ": " ^^ s);
    throw Error_internal_error()
}

val internal_error_caller : forall ('a : Type). (string, int, string) -> 'a

function internal_error_caller(f , l, k) -> 'a = {
    internal_error(f, l, k);
}

val main : unit -> unit

function main() = {
    internal_error_caller(__FILE__, __LINE__, "message 1");
    internal_error(__FILE__, __LINE__, "message 2");
}
