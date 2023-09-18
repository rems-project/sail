$include <prelude.sail>
$include <string.sail>

let x : int = 4

function main() -> unit = {
    let x = dec_str(x);
    print_endline(x);
}
