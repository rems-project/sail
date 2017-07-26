default Order dec

val forall Num 'n. (bit['n], int) -> bit effect pure vector_access

val forall Num 'n, Num 'm, Num 'o, 'm >= 'o, 'o >= 0, 'n >= 'm + 1.
  (bit['n], [:'m:], [:'o:]) -> bit['m - ('o - 1)] effect pure vector_subrange

register vector<32 - 1, 32, dec, bit>  _FPEXC32_EL2

val vector<32 - 1, 32, dec, bit>  -> unit effect {wreg} set_FPEXC32_EL2

function set_FPEXC32_EL2 value_name =
  {
    _FPEXC32_EL2[0..0] := [value_name[0]];
    _FPEXC32_EL2[1..1] := [value_name[1]];
    _FPEXC32_EL2[2..2] := [value_name[2]];
    _FPEXC32_EL2[3..3] := [value_name[3]];
    _FPEXC32_EL2[4..4] := [value_name[4]];
    _FPEXC32_EL2[6..5] := value_name[6 .. 5];
    _FPEXC32_EL2[7..7] := [value_name[7]];
    _FPEXC32_EL2[20..11] := value_name[20 .. 11];
    _FPEXC32_EL2[29..29] := [value_name[29]];
    _FPEXC32_EL2[30..30] := [value_name[30]]
  }

val unit -> vector<32 - 1, 32, dec, bit>  effect {rreg} get_FPEXC32_EL2

function get_FPEXC32_EL2 () =
  {
    (vector<32 - 1, 32, dec, bit> ) value_name := 0x04000700;
    value_name[0..0] := [_FPEXC32_EL2[0]];
    value_name[1..1] := [_FPEXC32_EL2[1]];
    value_name[2..2] := [_FPEXC32_EL2[2]];
    value_name[3..3] := [_FPEXC32_EL2[3]];
    value_name[4..4] := [_FPEXC32_EL2[4]];
    value_name[6..5] := _FPEXC32_EL2[6 .. 5];
    value_name[7..7] := [_FPEXC32_EL2[7]];
    value_name[20..11] := _FPEXC32_EL2[20 .. 11];
    value_name[26..26] := [_FPEXC32_EL2[26]];
    value_name[29..29] := [_FPEXC32_EL2[29]];
    value_name[30..30] := [_FPEXC32_EL2[30]];
    value_name
  }

val vector<32 - 1, 32, dec, bit>  -> unit effect {rreg, wreg} set_FPEXC

function set_FPEXC val_name =
  {
    (vector<32 - 1, 32, dec, bit> ) r := val_name;
    (vector<32 - 1, 32, dec, bit> ) __tmp_45 := get_FPEXC32_EL2();
    __tmp_45[31..0] := r;
    set_FPEXC32_EL2(__tmp_45)
  }
