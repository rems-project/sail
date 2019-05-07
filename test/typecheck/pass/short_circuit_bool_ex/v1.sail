default Order dec

$include <prelude.sail>
$include <string.sail>

val assertive : forall 'n. int('n) -> range(0,'n) effect {escape}

function assertive(n) = {
  assert(n > 0);
  0
}

val ok : unit -> bool(0 == 1) effect {escape}

function ok() = {
  let n = -1;
  let a = assertive(n) > 0 in
  if (true | a) then true else true
}

val bad : unit -> bool(0 == 1) effect {escape}

function bad() = {
  let n = -1;
  if (true | assertive(n) > 0) then true else true
}

val main : unit -> unit effect {escape}

function main() =
  if bad() then
    print_endline("0 = 1")
  else
    print_endline("0 != 1")