-- This module serves as the root of the `LeanRiscv` library.
-- Import modules here that should be built as part of the library.
import ELFSage
import LeanRV64DLEAN
import LeanRV64DLEAN.Sail.Sail

def readElf32 (elfFilepath : System.FilePath) : IO (Except String ELF32File) := do
  let bytes <- IO.FS.readBinFile elfFilepath
  match mkRawELFFile? bytes with
  | .error warning => do
    pure (.error warning)
  | .ok (.elf32 elf) => do
    -- IO.println s!"{repr elf}"
    pure (.ok elf)
  | .ok (.elf64 _elf) => do
    pure (.error "64 bit ELF file not supported")

inductive MachineBits where
  | B32
  | B64

def DEFAULT_RSTVEC := 0x00001000

def initializeMemory (_size: MachineBits) (elf : ELF32File) : Std.HashMap Nat (BitVec 8) :=
  -- From: sail-riscv/c_emulator/riscv_sim.cpp
  --
  -- let RST_VEC_SIZE : UInt32 := 8
  -- let is_32bit_model := match size with
  --   | .B32 => true
  --   | .B64 => false
  -- let entry : UInt64 := sorry
  -- -- Little endian
  -- let reset_vec : List UInt32 := [
  --   0x297,                                                     -- auipc  t0,0x0
  --   (0x28593 : UInt32) + (RST_VEC_SIZE * (4 : UInt32) <<< 20), -- addi   a1, t0, &dtb
  --   0xf1402573,                                                -- csrr   a0, mhartid
  --   if is_32bit_model then 0x0182a283                          -- lw     t0,24(t0)
  --                     else 0x0182b283,                         -- ld     t0,24(t0)
  --   0x28067,                                                   -- jr     t0
  --   0,
  --   UInt64.toUInt32 (entry &&& 0xffffffff),
  --   UInt64.toUInt32 (entry >>> 32)
  -- ]
  -- let rv_rom_base := DEFAULT_RSTVEC

  let update_mem_segment mem first_addr body :=
    let addrs := Array.range' first_addr (Array.size body)
    Array.foldl (λ mem (addr, byte) => 
      if mem.contains addr then
        panic s!"Address {addr} is already written to!"
      else
        mem.insert addr byte.toBitVec
    ) mem (Array.zip addrs body)

  -- Handle interpreted_segments
  let mem'' := List.foldl (λ mem (_header, inst) => 
          -- TODO(JP): Is this address correct?
          update_mem_segment mem inst.segment_base inst.segment_body.data
        ) default elf.interpreted_segments
  -- Handle interpreted_sections
  let mem' := mem''
  -- let mem' := List.foldl (λ mem (_header, inst) =>
  --         -- TODO(JP): Is this address correct?
  --         update_mem_segment mem inst.section_offset inst.section_body.data
  --       ) mem'' elf.interpreted_sections
  -- Handle bits_and_bobs
  let mem := List.foldl (λ mem (addr, data) =>
          update_mem_segment mem addr data.data
        ) mem' elf.bits_and_bobs

  mem

def initializeRegisters : Std.DHashMap Register RegisterType :=
  -- TODO: initialize register properly
  Std.DHashMap.empty

def my_main (_ : PUnit) :=
  open LeanRV64DLEAN.Functions in
  open Sail in
  do
  -- monadLift (IO.print "TEST")
  -- let _ <- pure (unsafeIO (IO.print "TEST"))
  dbg_trace "In my_main!"
  -- print_effect
  sail_main ()


def runElf32 (elf : ELF32File) : IO UInt32 :=
  open Sail in
  open LeanRV64DLEAN.Functions in
  let mem := initializeMemory MachineBits.B32 elf
  let regs := initializeRegisters
  let initialState := ⟨regs, (), mem, default, default, default⟩
  main_of_sail_main initialState (sail_model_init >=> my_main)
  -- main_of_sail_main initialState my_main
  

