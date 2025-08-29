
type bit =
| B0
| B1

type value =
| V_vector of value list
| V_list of value list
| V_int of Nat_big_num.num
| V_real of Rational.t
| V_bool of bool
| V_bit of bit
| V_tuple of value list
| V_unit
| V_string of string
| V_ref of string
| V_member of string
| V_ctor of string * value list
| V_record of (string * value) list
| V_attempted_read of string
