
let opt_interactive = ref false
let opt_suppress_banner = ref false

let env = ref Type_check.initial_env

let ast = ref (Ast.Defs [])
