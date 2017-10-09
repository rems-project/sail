
val extern int -> string effect pure string_of_int = "string_of_big_int"

val extern (int, int) -> int effect pure add = "add"
val extern (int, int) -> bool effect pure lt = "lt_int"

overload (deinfix +) [add]
overload (deinfix <) [lt]

val unit -> unit effect pure main

function main () = {
  (int) x := 0;
  while x < 100 do {
    x := x + 1;
    print(string_of_int(x))
  }
}
