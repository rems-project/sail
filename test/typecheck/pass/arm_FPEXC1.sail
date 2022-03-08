default Order dec

val vector_access = pure {ocaml: "access", lem: "access_vec_dec", coq: "access_vec_dec"}: forall ('n : Int).
  (bitvector('n, dec), int) -> bit

val vector_subrange = pure {ocaml: "subrange", lem: "subrange_vec_dec", coq: "subrange_vec_dec"}: forall ('n : Int) ('m : Int) ('o : Int), 'm >= 'o & 'o >= 0 & 'n >= 'm + 1.
  (bitvector('n, dec), atom('m), atom('o)) -> bitvector('m - ('o - 1), dec)

val vector_update_subrange = pure {ocaml: "update_subrange", lem: "update_subrange_vec_dec", coq: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (bitvector('n, dec), atom('m), atom('o), bitvector('m - ('o - 1), dec)) -> bitvector('n, dec)

register _FPEXC32_EL2 : bitvector(32, dec)

val set_FPEXC32_EL2 : bitvector(32, dec) -> unit effect {wreg}

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

val get_FPEXC32_EL2 : unit -> bitvector(32, dec) effect {rreg}

function get_FPEXC32_EL2 () = {
  value_name : bitvector(32, dec) = 0x04000700;
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

val set_FPEXC : bitvector(32, dec) -> unit effect {rreg, wreg}

function set_FPEXC val_name = {
  r : bitvector(32, dec) = val_name;
  __tmp_45 : bitvector(32, dec) = get_FPEXC32_EL2();
  __tmp_45[31 .. 0] = r;
  set_FPEXC32_EL2(__tmp_45)
}
