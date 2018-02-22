/* Moved and tightened an assertion */

val aarch64_memory_exclusive_pair : forall ('datasize : Int) ('regsize : Int) ('elsize : Int).
  (AccType, atom('datasize), atom('elsize), MemOp, int, bool, atom('regsize), int, int, int) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_exclusive_pair (acctype, datasize, elsize, memop, n, pair, regsize, s, t, t2) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  rt_unknown : bool = false;
  rn_unknown : bool = false;
  if (memop == MemOp_LOAD & pair) & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if memop == MemOp_STORE then {
    if s == t | pair & s == t2 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_DATAOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rt_unknown = true,
        Constraint_NONE => rt_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ();
    if s == n & n != 31 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_BASEOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rn_unknown = true,
        Constraint_NONE => rn_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ()
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else if rn_unknown then address = undefined
  else address = aget_X(n);
  secondstage : bool = undefined;
  iswrite : bool = undefined;
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined
      else if pair then let 'v = ex_int(datasize / 2) in {
        assert(constraint(2 * 'v = 'datasize));
        el1 : bits('v) = aget_X(t);
        el2 : bits('v) = aget_X(t2);
        data = if BigEndian() then el1 @ el2 else el2 @ el1
      } else data = aget_X(t);
      status : bits(1) = 0b1;
      if AArch64_ExclusiveMonitorsPass(address, dbytes) then {
        aset_Mem(address, dbytes, acctype, data);
        status = ExclusiveMonitorsStatus()
      } else ();
      aset_X(s, ZeroExtend(status, 32))
    },
    MemOp_LOAD => {
      AArch64_SetExclusiveMonitors(address, dbytes);
      if pair then
        if rt_unknown then aset_X(t, undefined : bits(32)) else if elsize == 32 then {
          assert(constraint(- 'elsize + 'datasize > 0 & 'elsize >= 0), "datasize constraint");
          data = aget_Mem(address, dbytes, acctype);
          if BigEndian() then {
            aset_X(t, slice(data, elsize, negate(elsize) + datasize));
            aset_X(t2, slice(data, 0, elsize))
          } else {
            aset_X(t, slice(data, 0, elsize));
            aset_X(t2, slice(data, elsize, negate(elsize) + datasize))
          }
        } else {
          if address != Align(address, dbytes) then {
            iswrite = false;
            secondstage = false;
            AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage))
          } else ();
          aset_X(t, aget_Mem(address + 0, 8, acctype));
          aset_X(t2, aget_Mem(address + 8, 8, acctype))
        }
      else {
        data = aget_Mem(address, dbytes, acctype);
        aset_X(t, ZeroExtend(data, regsize))
      }
    }
  }
}
