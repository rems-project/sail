$option -dmagic_hash

$project# A {} B { requires A }

$start_module# A

private scattered union U

union clause U = A : unit

$end_module#

$start_module# B

union clause U = B : unit

$end_module#
