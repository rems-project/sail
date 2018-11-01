$option -Xconstraint_synonyms

constraint Size('n) = 'n in {32, 64}

constraint Nat('n) = 'n >= 0

val foo : forall 'n, where Size('n). int('n) -> unit
