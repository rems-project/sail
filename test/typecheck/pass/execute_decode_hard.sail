default Order dec

$include <prelude.sail>

union ast('D: Int), 'D in {32, 64, 128} = {
  Instr1 : {'R, 'R in {32, 64}. (int('R), bits('D))}
}

val execute : forall 'd, 'd in {32, 64, 128}. ast('d) -> unit

function clause execute(Instr1(r as int('R), d)) = {
  _prove(constraint('R in {32, 64}));
  if length(d) == 64 then {
    let _ = d[r - 1 .. 0];
    ()
  }
}

function clause execute(Instr1((r as int('R), d))) = {
  _prove(constraint('R in {32, 64}));
  if length(d) == 64 then {
    let _ = d[r - 1 .. 0];
    ()
  }
}

