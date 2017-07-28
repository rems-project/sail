
typedef A = const struct {bool field_A; int shared}
typedef B = const struct {bool field_B; int shared}

val (bool, int) -> A effect {undef, wreg} makeA

function makeA (x, y) =
{
  (A) record := undefined;
  record.field_A := x;
  record.shared := y;
  record
}
