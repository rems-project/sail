default Order dec

$option --abstract-types
$option --config ../typecheck/pass/abstract_config.json

type xlen : Int = config arch.xlen

constraint xlen in {32, 64}

type have_thing : Bool = config arch.have_the_thing

constraint xlen in {16, 32}

type ylen : Int = config arch.ylen

constraint xlen <= ylen
