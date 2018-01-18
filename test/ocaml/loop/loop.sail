val string_of_int = "string_of_int" : int -> string

val add = "add" : (int, int) -> int

val lt = "lt_int" : (int, int) -> bool

overload operator + = {add}

overload operator < = {lt}

val main : unit -> unit

function main () = {
  x : int = 0;
  while x < 100 do {
    x = x + 1;
    print(string_of_int(x))
  }
}
