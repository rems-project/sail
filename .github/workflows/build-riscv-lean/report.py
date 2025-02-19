#!/usr/bin/env python3

f = open("LeanRV64DLEAN.lean")
linesmodel = f.readlines()

# The number of lines in the file
linecountmodel = len(linesmodel)
defcount = list(filter(lambda x: "def " in x, linesmodel))
inductivecount = list(filter(lambda x: "inductive " in x, linesmodel))
abbrevcount = list(filter(lambda x: "abbrev " in x, linesmodel))

f = open("build_log.txt")
lines = f.readlines()

errors = list(filter(lambda x: "error: " in x, lines))

# The number of lines containing the word "error"
errorcount = len(list(errors))

# The number of lines containing the word "warning"
warningcount = len(list(filter(lambda x: "warning: " in x, lines)))

# Remove anything before the string "error: " from each line
errors = list(map(lambda x: x[x.rfind(": ")+2:-1], errors))

# Create an array of unique errors plus their count from errors
errors = [[errors.count(x), x] for x in set(errors)]
errors.sort(reverse=True)

print(f"# RISC-V Lean Statistics\n")

print(f"Lines: {linecountmodel}  ")
print(f"Definitions: {len(defcount)}  ")
print(f"Inductive definitions: {len(inductivecount)}  ")
print(f"Abbreviations: {len(abbrevcount)}  ")

print("")
print("# Warnings and Errors\n")

print(f"Errors found: {errorcount}  ")
print(f"Warnings found: {warningcount}  ")

print("")
print("## Error Classes\n")

for error in errors:
    print(f"- {error[0]}x {error[1]}")


