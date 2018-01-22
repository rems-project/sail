
// Type synonym with a constraint.
type regno ('n : Int), 0 <= 'n < 32 = atom('n)

// Existential with constrained type synonym.
let x : {'n, 0 <= 'n <= 8. regno('n)} = 4

// Valspec with constrained type synonym.
val test : forall 'n, 0 <= 'n <= 100. regno('n) -> unit