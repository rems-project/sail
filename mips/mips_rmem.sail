/* These instructions are used for RMEM integration only */

/* Co-opt syscall 0xfffff for use as thread start in pccmem  */
union clause ast = SYSCALL_THREAD_START : unit
function clause decode (0b000000 @ 0xfffff @ 0b001100) =
  Some(SYSCALL_THREAD_START())
function clause execute (SYSCALL_THREAD_START()) = ()


/* fake stop fetching instruction for ppcmem, execute doesn't do anything,
   decode never produces it */

union clause ast = ImplementationDefinedStopFetching : unit
function clause execute (ImplementationDefinedStopFetching()) = ()

