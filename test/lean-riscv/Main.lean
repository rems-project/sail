import LeanRiscv

def main (args : List String) : IO UInt32 := do
  if args.length != 2 then do
    IO.println "usage: run-riscv-lean <elf_file>"

    pure 255
  else do
    -- Parse input elf file.
    let elfF <- readElf32 args[1]!
    
    pure 0
    -- TODO:
    -- Convert to Sail's AST
    -- Run program
