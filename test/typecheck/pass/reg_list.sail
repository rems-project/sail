register X : list(bool)

val init_X : unit -> unit effect {wreg}
function init_X () = {
  X = [||];
}

