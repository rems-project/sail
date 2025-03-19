-- This module serves as the root of the `LeanRiscv` library.
-- Import modules here that should be built as part of the library.
import ELFSage
-- import LeanRV64DLEAN
import LeanRV64DLEAN.Sail.Sail

def readElf32 (elfFilepath : System.FilePath) : IO (Except String ELF32File) := do
  let bytes <- IO.FS.readBinFile elfFilepath
  match mkRawELFFile? bytes with
  | .error warning => do
    pure (.error warning)
  | .ok (.elf32 elf) => do
    -- sorry
    IO.println s!"{repr elf}"
    pure (.ok elf)
  | .ok (.elf64 elf) => do
    pure (.error "64 bit ELF file not supported")


#check mkRawELFFile?
-- #check sail_model_init

-- open LeanRV64DLEAN.Sail.Sail
def runElf32 (elf : EF32File) : IO PUnit := do
    -- IO.println "TODO"
    let _ := sail_model_init
    main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)


  

