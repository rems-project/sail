
val test : bool -> unit

function test _ = ()

val main: unit -> unit

function main _ = {
  let test2 = true;
  test(test2)
}
