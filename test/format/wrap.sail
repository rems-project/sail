function clause ext_read_CSR 0x001 = Some(zero_extend(fcsr[FFLAGS]))
function clause ext_read_CSR 0x002 = Some(zero_extend(fcsr[FRM]))
function clause ext_read_CSR 0x003 = Some(zero_extend(fcsr.bits))


let a =
 1 // comment

let a = if i + rs1_val < VLMAX then { 1 } else { 2 }

function clause execute SINVAL_VMA(rs1, rs2) = {
  execute(SFENCE_VMA(rs1, rs2))
}

function effectivePrivilege(t : AccessType(ext_access_type), m : Mstatus, priv : Privilege) -> Privilege = if t !=
  Execute() &
  m[MPRV] ==
  0b1
then {
  privLevel_of_bits(m[MPP])
} else {
  priv
}

function init_pmp () -> unit = {
    assert(sys_pmp_count() == 0 | sys_pmp_count() == 16 | sys_pmp_count() == 64, "sys_pmp_count() must be 0, 16, or 64");

  X(rd) = if sizeof(xlen) < SEW
    then slice(vs2_val[0], 0, sizeof(xlen))
    else if sizeof(xlen) > SEW then sign_extend(vs2_val[0]) else vs2_val[0];
  
  misa[D] =

      if sizeof(flen) >= 64
      then
        bool_to_bits(sys_enable_fdext()) 
		//
      else 0b0;

  let update_d : bool =
    ((pte_flags[D]) == 0b0) &
      (match a {
      Execute() => false,
      Read() => false,
      Write(_) => true,
      ReadWrite(_, _) => true,
    });

  let result =
    (match read_kind_of_flags(aq, rl, res) {
      Some(rk) => Some(read_ram(rk, paddr, width, meta)),
      None() => None(),
    }) :
      option((bits(8 * 'n), mem_meta));

    foreach (i from 0 to 63) {
        // On reset the PMP register's A and L bits are set to 0 unless the plaform
        // mandates a different value.
        pmpcfg_n[i] = [pmpcfg_n[i] with
            A = pmpAddrMatchType_to_bits(OFF), L = 0b0
        ]
    }
}

register mtimecmp :
  bits(64) // memory-mapped internal clint register.

function not_implemented message =
  throw Error_not_implemented(message)


function valid_hex_bits_signed(n, str) = {
    if string_take(str, 1) == "-" then {
        valid_hex_bits(n, string_drop(str, longlonglonglonglong))
    } else {
        valid_hex_bits(n, longlonglonglonglong)
    }
}

function clause execute VMVXS(vs2, rd) = {
    X(rd) = if sizeof(xlen) < SEW then if sizeof(xlen) > SEW then sign_extenaaaaaaaaaaaaaaaaaaaaaaaad(vs2_val[0]) else lonaaaaaaaaaaaaaaaaaaglonggggg[0] else slice(vs2_val[0], 0, sizeof(xlen));
    
	X(rd) = if size < SEW 
	then if size > SEW 
	then si 
	else lon 
	else slice;

  if sizeof(xlen) == 64 then {
    mstatus =     Mk_Mstatus([mstatus.bits with 37 .. 36 = 0b00])
  };

    RETIRE_SUCCESS
}

function clause execute RISCV_FLI_H(constantidx, rd) = {
  let bits : bits(16) = match constantidx {
    0b00001 => { 0xbc00 /* -1.0 */ },
    0b00011 => { 0xbc00 /* -1.0 */ },
    0b00111 => { 0xbc00 /* -1.0 */ },
    0b01111 => { 0xbc00 /* -1.0 */ },
  }
}
