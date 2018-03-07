
scattered union exception

union clause exception = Test_int : int

union clause exception = Test_failure : string

val main : unit -> unit effect {escape}

function main () = {
  try {
    print("Before throw");
    throw(Test_failure("Caught!"));
    print("Not printed")
  } catch {
    Test_failure(msg) => print(msg),
    _ => print("Unknown exception")
  }
}

union clause exception = Test_other : unit

end exception