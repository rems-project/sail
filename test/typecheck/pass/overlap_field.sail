struct A = {field_A : bool, shared : int}

struct B = {field_B : bool, shared : int}

val makeA : (bool, int) -> A effect {undef}

function makeA (x, y) = {
  record : A = undefined;
  record.field_A = x;
  record.shared = y;
  record
}
