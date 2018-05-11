$include <flow.sail>
$include <vector_inc.sail>

enum signal = {LOW, HIGH}

type Bit32 = vector(32, inc, bit)

struct Record = {rsig : signal, bitf : Bit32}

register R0 : vector(32, inc, bit)

val test : Record -> unit effect {wreg}

function test r : Record = R0 = r.bitf
