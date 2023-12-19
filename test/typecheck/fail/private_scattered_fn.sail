$option -dmagic_hash

$project# A {} B { requires A }

$start_module# A

private val f : int -> int

scattered function f

function clause f 2 = 3

$end_module#

$start_module# B

function clause f _ = 0

$end_module#
