default Order dec

val vector_access = {ocaml: "access", lem: "access_vec_dec", coq: "access_vec_dec"}: forall ('n : Int).
  (vector('n, dec, bit), int) -> bit

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec", coq: "subrange_vec_dec"}: forall ('n : Int) ('m : Int) ('o : Int), 'm >= 'o & 'o >= 0 & 'n >= 'm + 1.
  (vector('n, dec, bit), atom('m), atom('o)) -> vector('m - ('o - 1), dec, bit)

val vector_update_subrange = {ocaml: "update_subrange", lem: "update_subrange_vec_dec", coq: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (vector('n, dec, bit), atom('m), atom('o), vector('m - ('o - 1), dec, bit)) -> vector('n, dec, bit)

register _FPEXC32_EL2 : vector(32, dec, bit)

val set_FPEXC32_EL2 : vector(32, dec, bit) -> unit effect {wreg}

function set_FPEXC32_EL2 value_name = {
  _FPEXC32_EL2[0 .. 0] = [value_name[0]];
  _FPEXC32_EL2[1 .. 1] = [value_name[1]];
  _FPEXC32_EL2[2 .. 2] = [value_name[2]];
  _FPEXC32_EL2[3 .. 3] = [value_name[3]];
  _FPEXC32_EL2[4 .. 4] = [value_name[4]];
  _FPEXC32_EL2[6 .. 5] = value_name[6 .. 5];
  _FPEXC32_EL2[7 .. 7] = [value_name[7]];
  _FPEXC32_EL2[20 .. 11] = value_name[20 .. 11];
  _FPEXC32_EL2[29 .. 29] = [value_name[29]];
  _FPEXC32_EL2[30 .. 30] = [value_name[30]]
}

val get_FPEXC32_EL2 : unit -> vector(32, dec, bit) effect {rreg}

function get_FPEXC32_EL2 () = {
  value_name : vector(32, dec, bit) = 0x04000700;
  value_name[0 .. 0] = [_FPEXC32_EL2[0]];
  value_name[1 .. 1] = [_FPEXC32_EL2[1]];
  value_name[2 .. 2] = [_FPEXC32_EL2[2]];
  value_name[3 .. 3] = [_FPEXC32_EL2[3]];
  value_name[4 .. 4] = [_FPEXC32_EL2[4]];
  value_name[6 .. 5] = _FPEXC32_EL2[6 .. 5];
  value_name[7 .. 7] = [_FPEXC32_EL2[7]];
  value_name[20 .. 11] = _FPEXC32_EL2[20 .. 11];
  value_name[26 .. 26] = [_FPEXC32_EL2[26]];
  value_name[29 .. 29] = [_FPEXC32_EL2[29]];
  value_name[30 .. 30] = [_FPEXC32_EL2[30]];
  value_name
}

val set_FPEXC : vector(32, dec, bit) -> unit effect {rreg, wreg}

function set_FPEXC val_name = {
  r : vector(32, dec, bit) = val_name;
  __tmp_45 : vector(32, dec, bit) = get_FPEXC32_EL2();
  __tmp_45[31 .. 0] = r;
  set_FPEXC32_EL2(__tmp_45)
}
