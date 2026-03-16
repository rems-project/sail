
type bit =
| B0
| B1

(** val bit_eqb : bit -> bit -> bool **)

let bit_eqb lhs rhs =
  match lhs with
  | B0 -> (match rhs with
           | B0 -> true
           | B1 -> false)
  | B1 -> (match rhs with
           | B0 -> false
           | B1 -> true)
