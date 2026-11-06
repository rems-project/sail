
$include <arith.sail>
$include <real.sail>

val main : unit -> unit

function main() = {
  let x : real = 16.0;
  print_real("1: ", x);
  print_int("1: ", floor(x));
  print_int("1: ", ceil(x));
  print_real("1: ", sqrt(x));
  print_int("1: ", floor(sqrt(x)));
  print_int("1: ", ceil(sqrt(x)));
  let x : real = 17.0;
  print_real("2: ", x);
  print_int("2: ", floor(x));
  print_int("2: ", ceil(x));
  print_real("2: ", sqrt(x));
  print_int("2: ", floor(sqrt(x)));
  print_int("2: ", ceil(sqrt(x)));
  let x : real = 0.00000000015;
  print_real("3: ", sqrt(x));
  let x : real = 57220458984375.0 / 123665200736552267030251260509823595017565674550605919957031528046448612553265933585158200530621522494798835713008069669675682517153375604983773077550946583958303386074349568.0;
  print_real("4: ", sqrt(x));
}
