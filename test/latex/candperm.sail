/* Test that we can parse the CAndPerm documentation correctly:
 * Previously the \hyperref expressions were broken. */  
default Order dec

scattered union ast('datasize : Int, 'destsize : Int, 'regsize : Int)
val execute : forall ('datasize : Int) ('destsize : Int) ('regsize : Int).
  ast('datasize, 'destsize, 'regsize) -> unit
scattered function execute
/*! CAndPerm union clause documentation */
union clause ast = CAndPerm : (int, int, int)
/*!
 * Capability register \emph{cd} is replaced with the contents of capability
 * register \emph{cs1} with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register \emph{rs2}
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits \hyperref[table:pseudocode-constants]{\emph{first\_uperm}} ..
 * \hyperref[table:pseudocode-constants]{\emph{last\_uperm}} of \emph{rd}.
 */
function clause execute(CAndPerm(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}
/* Note: need at least two function clauses to generate latex output */
union clause ast = CSetFlags : (int, int, int)
function clause execute CSetFlags(cd, cs1, rs2) = return(())

end execute
end ast
