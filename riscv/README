Booting Linux with the C backend:
---------------------------------

The C model needs an ELF-version of the BBL (Berkeley-Boot-Loader) that contains
the Linux kernel as an embedded payload.  It also needs a DTB (device-tree blob)
file describing the platform.  Once those are available, the model should be run
as:

$ ./riscv_sim -b spike.dtb bbl > execution-trace.log 2>&1 &
$ tail -f term.log

The term.log file contains the console boot messages.


Booting Linux with the OCaml backend:
-------------------------------------

The OCaml model only needs the ELF-version of the BBL, since it can generate its
own DTB.

$ ./platform bbl > execution-trace.log

The console output is sent to stderr.
