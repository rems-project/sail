default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

val main : unit -> unit

register r : list(list(int)) = [||]

function main() = {
  let x : list(list(int)) = [|[|1|], [|2, 3|]|];
  r = [|2, 3|] :: [||];
  r = [|1|] :: r;
  assert(x == r);
  print_endline("ok");
}
