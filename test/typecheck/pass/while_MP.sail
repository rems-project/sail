default Order dec

val extern (int, int) -> int effect pure add_int = "add"
overload (deinfix +) [add_vec_int; add_range; add_int]

val extern bool -> bool effect pure bool_not = "not"

register (bool) INT

function (int) test () = {
  (int) count := 0;
  while (bool_not(INT)) do {
    count := count + 1;
  };
  return count;
}

