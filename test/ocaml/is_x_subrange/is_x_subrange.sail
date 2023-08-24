/* Uncomment for stand-alone test
default Order dec

$include <prelude.sail>
*/
$include <mono_rewrites.sail>

val main : unit -> unit

function main() = {
    let a = 0xffff;
    if is_zero_subrange(a, 3, 1) then print_endline("abc") else print_endline("def");
    if is_ones_subrange(a, 3, 1) then print_endline("abc") else print_endline("def");
}
