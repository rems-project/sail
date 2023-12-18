$option -dmagic_hash

$project# A {} B { requires A } C { requires B }

$start_module# A

scattered enum E
enum clause E = E_one

$end_module#

$start_module# B

enum clause E = E_two

$end_module#

$start_module# C

enum clause E = E_three

$end_module#
