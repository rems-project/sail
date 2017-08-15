
scattered typedef exception = const union

union exception member int IntEx

val unit -> unit effect {escape} test2

function test2 () = throw (IntEx(3))

val unit -> unit effect {escape} test

function test () =
  try {
    test2();
    ()
  } catch {
    case (IntEx(_)) -> ()
  }

end exception
