
type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint
| Da of uint
| Db of uint
| Dc of uint
| Dd of uint
| De of uint
| Df of uint

type signed_int =
| Pos of uint
| Neg of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')
  | Da d0 -> revapp d0 (Da d')
  | Db d0 -> revapp d0 (Db d')
  | Dc d0 -> revapp d0 (Dc d')
  | Dd d0 -> revapp d0 (Dd d')
  | De d0 -> revapp d0 (De d')
  | Df d0 -> revapp d0 (Df d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> Da (double d0)
  | D6 d0 -> Dc (double d0)
  | D7 d0 -> De (double d0)
  | D8 d0 -> D0 (succ_double d0)
  | D9 d0 -> D2 (succ_double d0)
  | Da d0 -> D4 (succ_double d0)
  | Db d0 -> D6 (succ_double d0)
  | Dc d0 -> D8 (succ_double d0)
  | Dd d0 -> Da (succ_double d0)
  | De d0 -> Dc (succ_double d0)
  | Df d0 -> De (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> Db (double d0)
  | D6 d0 -> Dd (double d0)
  | D7 d0 -> Df (double d0)
  | D8 d0 -> D1 (succ_double d0)
  | D9 d0 -> D3 (succ_double d0)
  | Da d0 -> D5 (succ_double d0)
  | Db d0 -> D7 (succ_double d0)
  | Dc d0 -> D9 (succ_double d0)
  | Dd d0 -> Db (succ_double d0)
  | De d0 -> Dd (succ_double d0)
  | Df d0 -> Df (succ_double d0)
 end
