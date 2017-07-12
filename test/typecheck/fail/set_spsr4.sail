default Order dec

val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'l >= 0, 'm <= 'o, 'o <= 'l.
  (vector<'n,'l,inc,'a>, [:'m:], [:'o:]) -> vector<'m,'o - 'm,inc,'a> effect pure vector_subrange_inc

val forall Nat 'n, Nat 'l, Nat 'm, Nat 'o, Type 'a, 'n >= 'm, 'm >= 'o, 'o >= 'n - 'l + 1.
  (vector<'n,'l,dec,'a>, [:'m:], [:'o:]) -> vector<'m,'m - 'o - 1,dec,'a> effect pure vector_subrange_dec

overload vector_subrange [vector_subrange_inc; vector_subrange_dec]

register bit[31] SPSR_EL2

function unit set_SPSR_hyp (bit[32]) val_name =
{
  (bit[32]) r := val_name;
  SPSR_EL2[31..0] := r
}
