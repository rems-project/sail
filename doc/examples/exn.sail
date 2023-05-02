default Order dec
$include <string.sail>

$span start EXN
scattered union exception

union clause exception = Epair : (range(0, 255), range(0, 255))

union clause exception = Eunknown : string

function main() : unit -> unit = {
    try {
        throw(Eunknown("foo"))
    } catch {
        Eunknown(msg) => print_endline(msg),
        _ => exit()
    }
}

union clause exception = Eint : int

end exception
$span end
