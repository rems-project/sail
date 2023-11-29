$option -dmagic_hash

$project# variable mods = [A] A {} B { requires $mods }

$start_module# A

let x : int = 3

$end_module# A

$start_module# B

let y : int = x

$end_module# B
