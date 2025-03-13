-- This module serves as the root of the `LeanRiscv` library.
-- Import modules here that should be built as part of the library.
import ELFSage

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
