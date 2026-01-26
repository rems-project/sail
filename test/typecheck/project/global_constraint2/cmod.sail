
type z : Int

constraint z <= y

val main : unit -> unit

function main() = {
  _prove(constraint(z <= 64))
}
