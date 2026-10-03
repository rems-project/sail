default Order dec

$include <prelude.sail>
$include <string.sail>

enum E1 = {A1, B1}
enum E2 = {A2, B2}
enum E3 = {A3, B3}

val m12 : E1 <-> E2
val m23 : E2 <-> E3

mapping m12 = { A1 <-> A2, B1 <-> B2 }
mapping m23 = { A2 <-> A3, B2 <-> B3 }

val m13 : E1 <-> E3

mapping m13 = { e <-> m23(m12(e)) }

val main : unit -> unit

function main() = {
    match m13(A1) {
        A3 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match m13(B1) {
        B3 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match m13(A3) {
        A1 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match m13(B3) {
        B1 => print_endline("ok"),
        _ => print_endline("fail"),
    }
}