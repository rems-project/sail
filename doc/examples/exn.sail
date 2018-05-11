val print = {ocaml: "print_endline"} : string -> unit

scattered union exception

union clause exception = Epair : (range(0, 255), range(0, 255))

union clause exception = Eunknown : string

function main() : unit -> unit = {
  try {
    throw(Eunknown("foo"))
  } catch {
    Eunknown(msg) => print(msg),
    _ => exit()
  }
}

union clause exception = Eint : int

end exception
