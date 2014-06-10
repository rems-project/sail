#!/bin/sh

# directory of our Power ISA to Sail generator
POWERISA="../../../rsem/idl/power"
# restricted set of instructions to translate
MNEMO="stwu,stw,mr,addi,lwz,bclr,or"

REBUILD=0

run () {
  printf "\n# $1\n"
  printf "$ $2"
  read ignore
  eval $2
}

while getopts ":r" opt; do
  case $opt in
    r)
      REBUILD=1
      ;;
    \?)
      echo "Invalid option: -$OPTARG" >&2
      ;;
  esac
done

rebuild () {
  run "Building Sail" "make clean sail lib"

  run "Generating the Sail interpreter from Power ISA (restricted to: $MNEMO)" \
    "make -C $POWERISA clean extract EXPORT_MNEMO=$MNEMO"

  run  "Type-checking Sail Power model" "make -C $POWERISA check"
  run  "Copying Power model locally to run tests" \
    "cp $POWERISA/generated/extract-full.sail test/power.sail"
  #git diff test/power.sail

  run  "Translating Power model from Sail to OCaml via Lem" "make power"
}

DEMO="./run_power.native --interactive --file test/main.bin"

if [ $REBUILD -eq 1 ]; then
  rebuild
  run  "Starting interactive interpreter (press 'h' for help)" \
    "$DEMO"
else
  $DEMO
fi
