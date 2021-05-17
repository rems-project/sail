default Order dec

scattered union ast('datasize : Int, 'destsize : Int, 'regsize : Int)
val execute : forall ('datasize : Int) ('destsize : Int) ('regsize : Int).
  ast('datasize, 'destsize, 'regsize) -> unit

/* Note: need at least two function clauses to generate latex output */
scattered function execute
/*
 * The naive copy-paste of the existing latex fails due to [] being interpreted as a link.
 */
union clause ast = CAndPermBroken : (int, int, int)
/*!
 * Capability register \emph{cd} is replaced with the contents of capability
 * register \emph{cs1} with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register \emph{rs2}
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits \hyperref[table:pseudocode-constants]{\emph{first\_uperm}} ..
 * \hyperref[table:pseudocode-constants]{\emph{last\_uperm}} of \emph{rd}.
 */
function clause execute(CAndPermBroken(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}
union clause ast = CAndPermEscaped : (int, int, int)
/*!
 * Capability register \emph{cd} is replaced with the contents of capability
 * register \emph{cs1} with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register \emph{rs2}
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits \hyperref\[table:pseudocode-constants\]{\emph{first\_uperm}} ..
 * \hyperref\[table:pseudocode-constants\]{\emph{last\_uperm}} of \emph{rd}.
 */
function clause execute(CAndPermEscaped(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}

union clause ast = CAndPermMarkdown : (int, int, int)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register *rs2*
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits [*first_uperm*][<table:pseudocode-constants>] ..
 * [*last_uperm*][<table:pseudocode-constants>] of *rd*.
 */
function clause execute(CAndPermMarkdown(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}

union clause ast = CAndPermMarkdownWithRefMacro : (int, int, int)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register *rs2*
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits \firstUPerm{} .. \lastUPerm{} of *rd*.
 */
function clause execute(CAndPermMarkdownWithRefMacro(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}

union clause ast = CAndPermMarkdownWithExceptions : (int, int, int)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the \cperms{} field set to the bitwise-AND of
 * its previous value and bits 0 .. 10 of integer register *rs2*
 * and the \cuperms{} field set to the bitwise and of its previous value
 * and bits \firstUPerm{} .. \lastUPerm{} of *rd*.
 *
 * ### Exceptions:
 * An exception is raised if:
 *   - *cs1.tag* is not set.
 *   - *cs1* is sealed.
 */
function clause execute(CAndPermMarkdownWithExceptions(cd, cs1, rs2)) = {
    /* Implementation */
    return ()
}

end execute
end ast
