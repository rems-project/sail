open Datatypes

(** val compare : char -> char -> comparison **)

let compare = fun c1 c2 ->
    let cmp = Char.compare c1 c2 in
    if cmp < 0 then Lt else if cmp = 0 then Eq else Gt
