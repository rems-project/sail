#!/bin/sh

# directory of our Power ISA to Sail generator
POWERISA="../../../rsem/idl/power"
# restricted set of instructions to translate
MNEMO="stwu,stw,mr,addi,lwz,bclr,or"

run () {
  printf "\n# $1\n"
  printf "$ $2"
  read ignore
  eval $2
}

run "Building Sail" "ocamlbuild sail.native"

run "Generating the Sail interpreter from Power ISA (restricted to: $MNEMO)" \
  "make -C $POWERISA clean extract EXPORT_MNEMO=$MNEMO"

run  "Type-checking Sail Power model" "make -C $POWERISA check"
run  "Copying Power model locally to run tests" \
  "cp $POWERISA/generated/extract-full.sail test/power.sail"
#git diff test/power.sail

run  "Translating Power model from Sail to OCaml via Lem" "ocamlbuild test/run_power.native"

run  "Starting interactive interpreter (press 'h' for help)" \
  "./run_power.native --interactive --file test/main.bin"
