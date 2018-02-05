
val test : bool -> unit

function test _ = ()

val main: unit -> unit

function main _ = {
  let test = true;
  test(test)
}
