$option -dmagic_hash

$project# A {} B { requires A } C { requires B }

$start_module# A

scattered union U

union clause U = U1 : unit

$end_module#

$start_module# B

union clause U = U2 : int

$end_module#

$start_module# C

union clause U = U3 : string

$end_module#
