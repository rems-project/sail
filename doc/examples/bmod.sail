
$span start BRAVO
val bravo : unit -> unit

function bravo() = {
    let x = alfa();
    print_int("alfa returned: ", x)
}
$span end
