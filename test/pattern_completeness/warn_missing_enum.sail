enum E = A | C | D

function missing_enum_member(x: E) -> unit = {
    match x {
        A => (),
        B => (),
        C => (),
        D => (),
    }
}
