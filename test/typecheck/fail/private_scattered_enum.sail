$option --dallow-internal

$project# A {} B { requires A }

$start_module# A

private scattered enum E

enum clause E = A

$end_module#

$start_module# B

enum clause E = B

$end_module#
