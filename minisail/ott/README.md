# MiniSail+ Ott Definitions

Contains Ott definitions for MiniSail+ that defines the
syntax and type system for a subset of Sail.
This subset can handle most of the Sail prelude and
syntactically the RISCV model.

## Files

* minisailplus_ast_vct.ott - Syntax for values, constraints and types.
* minisailplus_ast_ped.ott - Syntax for patterns, expressions and definitions.
* minisailplus_rules.ott - Typing rules.

## Notes

1. The syntax for types follows the style for refinement types, ie { z : base | constraint }
rather than the special Sail format. Work is in-progress to describe how to convert from the
latter to the former.

2. The typing rules have a bidirectional and hence algorithmic flavour. Of note is the
use the klist nonterminal (`little gamma') that contains type information for sub-terms of terms.

3. For Coq prover backend, the definition of the necessary homs is complete but
the Coq functions are stubs.

4. These definitions are part a larger work and so include what might be considered noise
when viewed on their own. For example, the superscripts on the non-terminals in the PDF
are so that we can distinguish between MiniSail and Sail when describing elaboration
(which isn't included here). This case can be handled with `comment-filtering'.

5. What isn't described, and plays and important role, is the validity judgement |=. This is
the point at which an SMT problem is generated and SMT invoked as part of
subtype checking.

6. Coq prover files require the Ott Coq support library installed from OPAM. This can be install using 'opam install coq-ott'.
It has been tested with Coq 8.5 through 8.10.0.

