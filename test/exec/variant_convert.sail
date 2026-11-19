default Order dec

$include <prelude.sail>

union opt('a: Type) = {
  Val: 'a,
  Nothing: unit,
}

union res('a: Type) = {
  Ok: 'a,
  Msg: string,
}

val wrap : forall 'n, 'n > 0. (bool, bits('n)) -> opt(bits('n))

function wrap(b, x) = if b then Val(x) else Nothing()

val check : forall 'n, 'n > 0. (bool, bits('n)) -> res(bits('n))

function check(b, x) = if b then Ok(x) else Msg("bad")

function main() -> unit = {
  let a : opt(bits(64)) = wrap(true, 0x0123456789abcdef);
  match a {
    Val(v) => print_bits("a = ", v),
    Nothing() => print_endline("a = nothing"),
  };
  let b : opt(bits(8)) = wrap(false, 0xff);
  match b {
    Val(v) => print_bits("b = ", v),
    Nothing() => print_endline("b = nothing"),
  };
  let c : res(bits(32)) = check(true, 0xdeadbeef);
  match c {
    Ok(v) => print_bits("c = ", v),
    Msg(s) => print_endline(s),
  };
  let d : res(bits(16)) = check(false, 0x1234);
  match d {
    Ok(v) => print_bits("d = ", v),
    Msg(s) => print_endline(s),
  }
}
