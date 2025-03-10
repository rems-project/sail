default Order dec

$include <prelude.sail>

$iftarget c
$c_in_main sail_config_set_file("config_vec_list.json");
$c_in_main_post sail_config_cleanup();
$else
$option --config ../c/config_vec_list.json
$endif

val print_list : list(string) -> unit

function print_list [||] = ()
and print_list (hd :: tl) = {
    print_endline(hd);
    print_list(tl)
}

val main : unit -> unit

function main() = {
    let ys : list(string) = config foo.bar;
    let xs : {'n, 'n >= 2. vector('n, string)} = config foo.bar;
    foreach (n from 0 to (length(xs) - 1)) {
        print_endline(xs[n])
    };
    print_list(ys)
}
