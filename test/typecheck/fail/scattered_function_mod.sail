$option -dmagic_hash

$project# A {} B { requires A } C { requires B }

$start_module# A

val f : int -> int

scattered function f

function clause f 1 = 2

$end_module#

$start_module# B

function clause f 2 = 3

$end_module#

$start_module# C

function clause f _ = 0

$end_module#
