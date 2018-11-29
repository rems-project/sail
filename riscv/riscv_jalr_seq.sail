/* The definition for the sequential model. */

function clause execute (RISCV_JALR(imm, rs1, rd)) = {
/* For the sequential model, the memory-model definition doesn't work directly
   if rs1 = rd.  We would effectively have to keep a regfile for reads and another for
   writes, and swap on instruction completion.  This could perhaps be optimized in
   some manner, but for now, we just keep a reordered definition to improve simulator
   performance.
*/
  let newPC : xlenbits = (X(rs1) + EXTS(imm))[63..1] @ 0b0;
  if newPC[1] & (~ (haveRVC())) then {
    handle_mem_exception(newPC, E_Fetch_Addr_Align);
    false;
  } else {
    X(rd) = nextPC;
    nextPC = newPC;
    true
  }
}
