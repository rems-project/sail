$option -dmagic_hash

$rigging# variable b = false A {} B { requires if $b then A else [] }

$start_module# A

let x : int = 3

$end_module# A

$start_module# B

let y : int = x

$end_module# B
