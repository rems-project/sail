$option -dmagic_hash

$project# A {} B { requires A }

$start_module# A

private val m : int <-> string

scattered mapping m

mapping clause m = 0 <-> "0"

$end_module#

$start_module# B

mapping clause m = 1 <-> "1"

$end_module#
