$sail_internal

union option ('a : Type) = {None : unit, Some : 'a}

function gen() -> option(nat) = None()

function wrap_broken() -> option((nat, nat)) = {
  match (gen()) {
    Some(i)  => let r = (i, i) in Some(r),  /* works */
    Some(i) => Some((i, i)), /* doesn't work */
    None()  => None()
  }
}
