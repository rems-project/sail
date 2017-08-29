val extern (int, int) -> int effect pure add_int = "add"
overload (deinfix +) [ add_int ]

val extern (int, int) -> int effect pure sub_int = "sub"
overload (deinfix -) [ sub_int ]

function (int) foo ((int) w) = {
  (int) x := w;
  (int) y := w;
  foreach (z from 0 to 10) {
    x := x + z;
    y := y - z;
  };
  x + y;
}
