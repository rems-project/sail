default Order dec

$include <prelude.sail>
$include <mapping.sail>

type labels = list((string, int))

val assoc : forall ('a : Type). (list((string, 'a)), string) -> option('a)

function assoc(map, key) = {
  match map {
    (key', value) :: map if key == key' => Some(value),
    _ :: map => assoc(map, key),
    [||] => None()
  }
}

mapping label forall 'size, 'size > 0. (n: int, labels: labels, size: int('size)) -> string <-> bits('size) = {
  x <- bits(size) <-> x,
  forwards l =>
    match assoc(labels, l) {
      Some(offset) => get_slice_int(size, offset - n, 0),
      None() => sail_zeros(size)
    }
}

union ast = {
  Branch : (bits(16)),
  Add : (bits(5), bits(5), bits(5)),
  CAdd : (bits(3), bits(3), bits(3)),
  Label : string
}

val instruction_bytes : ast -> {|0, 2, 4|}

function instruction_bytes instr =
  match instr {
    Branch(_) => 4,
    Add(_) => 4,
    CAdd(_) => 2,
    Label(_) => 0
  }

mapping assembly(n: int, labels: labels) -> string <-> ast = {
  "b" ^ spc() ^ offset <- label(n, labels, 16) <-> Branch(offset),
  "add" ^ spc() ^ dst <- bits(5) ^ sep() ^ src1 <- bits(5) ^ sep() ^ src2 <- bits(5) <-> Add(dst, src1, src2),
  "c.add" ^ spc() ^ dst <- bits(3) ^ sep() ^ src1 <- bits(3) ^ sep() ^ src2 <- bits(3) <-> CAdd(dst, src1, src2),
  l ^ ":" <-> Label(l)
}

val get_labels : (list(string), int, labels) -> labels

function get_labels(instrs, n, labels) = {
  match instrs {
    [||] => labels,
    instr :: instrs =>
      match assembly(0, [||], instr) {
	Label(str) => get_labels(instrs, n, (str, n) :: labels),
	instr => get_labels(instrs, n + instruction_bytes(instr), labels)
      }
  }
}

val assemble_with_labels : (int, list(string), labels) -> list(ast)

function assemble_with_labels(n, toks, labels) = {
  match toks {
    [||] => [||],
    tok :: toks => {
      let instr = assembly(n, labels, tok);
      instr :: assemble_with_labels(n + instruction_bytes(instr), toks, labels)
    }
  }
}

function assemble(toks: list(string)) -> list(ast) = {
  let labels = get_labels(toks, 0, [||]);
  assemble_with_labels(0, toks, labels)
}
