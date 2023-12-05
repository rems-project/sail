# Sail Internals

## Abstract Syntax Tree

The Sail abstract syntax tree (AST) is defined by an ott grammar in
[sail.ott](https://github.com/rems-project/sail/blob/sail2/language/sail.ott). This
generates a OCaml (and lem) version of the ast in `src/ast.ml` and
`src/ast.lem`. Technically the OCaml version of the AST is generated
by [Lem](https://github.com/rems-project/lem), which allows the Sail
OCaml source to seamlessly interoperate with parts written in
Lem. Although we do not make much use of this, in principle it allows
us to implement parts of Sail in Lem, which would enable them to be
verified in Isabelle or HOL4.

The Sail AST looks something like:

```OCaml
and 'a exp =
 | E_aux of ( 'a exp_aux) * 'a annot

and 'a exp_aux =  (* expression *)
 | E_block of ( 'a exp) list (* sequential block *)
 | E_id of id (* identifier *)
 | E_lit of lit (* literal constant *)
 | E_typ of typ * ( 'a exp) (* cast *)
 | E_app of id * ( 'a exp) list (* function application *)
 | E_tuple of ( 'a exp) list (* tuple *)
 | E_if of ( 'a exp) * ( 'a exp) * ( 'a exp) (* conditional *)
 ...
```

Each constructor is prefixed by a unique code (in this case `E` for
expressions), and is additionally wrapped by an *aux* constructor
which attaches an annotation to each node in the AST, consisting of an
arbitrary type that parameterises the AST, and a location identifying
the position of the AST node in the source code:

```OCaml
type 'a annot = l * 'a
```

There are various types of locations:

```OCaml
type l =
  | Unknown
  | Unique of int * l
  | Generated of l
  | Range of Lexing.position * Lexing.position
  | Documented of string * l
```

`Range` defines a range of positions given by the parser, the
`Documented` constructor attaches doc-comments to
locations. `Generated` is used to signify that code is generated based
on code from some other location. `Unique` is used internally to tag
locations with unique integers so they can be referred to
later. `Unknown` is used for Sail that has no obvious corresponding
location, although this should be avoided as much possible as it leads
to poor error messages. Ast nodes programmatically generated initially
have `Unknown` locations, but `Ast_util.locate` can be used to
recursively attach `Generated` locations for error purposes.

A convention in the Sail source is that a single variable `l` is
always a location, usually the closest location.

### AST utilities

There are various functions for manipulating the AST defined in
[ast_util](https://github.com/rems-project/sail/blob/sail2/src/ast_util.mli). These
include constructor functions like `mk_exp` for generating untyped
expressions and various functions for destructuring AST nodes. It also
defines various useful Sets and Maps, e.g. sets of identifiers, type
variables etc. Note that type variables in Sail are often internally
referred to as *kids*, I think this is because type variables are
defined as having a specific *kind*, i.e. `'n : Int` is a type
variable with kind `Int`. (Although `kinded_id` is technically a
separate type which is a type variable * kind pair).

### Parse AST

There is a separate AST
[parse_ast.ml](https://github.com/rems-project/sail/blob/sail2/src/parse_ast.ml)
which the parser generates. It is very similar to the main AST except
it contains some additional syntactic sugar. The parse ast is
desugared by the
[initial_check](https://github.com/rems-project/sail/blob/sail2/src/initial_check.mli)
file, which performs some basic checks in addition from mapping the
parse AST to the main AST.

## Overall Structure

The main entry point for Sail is the file
[sail.ml](https://github.com/rems-project/sail/blob/sail2/src/sail.ml). Each
backend option e.g. `-c`, `-lem`, `-ocaml` etc, is referred to as a
*target*, and the `set_target` function is used to set the
`opt_target` variable, for example

```OCaml
  ( "-c",
    Arg.Tuple [set_target "c"; Arg.Set Initial_check.opt_undefined_gen],
    " output a C translated version of the input");
```

defines the `-c` option. Each Sail option is configured via via `opt_`
variables defined at the top of each relevant file. In this case we
tell Sail that when we generate C, we also want to generated
`undefined_X` functions for each type `X`. In general such `opt_`
variables should be set when we start Sail and remain immutable
thereafter.

The first function called by `main` is `Sail.load_files`. This
function parses all the files passed to Sail, and then concatenates
their ASTs. The pre-processor is then run, which evaluates `$directive`
statements in Sail, such as

```
$include <prelude.sail>
```

Unlike the C pre-processor the Sail pre-processor operates over actual
Sail ASTs rather than strings. This can recursively include other
files into the AST, as well as add/remove parts of the AST with
`$ifdef` etc. Directives that are used are preserved in the AST, so
they also function as a useful way to pass auxiliary information to
the various Sail backends.

The initial check mentioned above is then run to desugar the AST, and
then the type-checker is run which produces a fully type-checked
AST. Type annotations are attached to every node (for which an
annotation makes sense) using the aux constructors. The type-checker
is discussed in more details later.

After type-checking the Sail scattered definitions are de-scattered
into single functions.

All the above is shared by each target and performed by the
`load_files` function.

The next step is to apply various target-specific rewrites to the AST
before passing it to the backend for each target.

The file
[rewrites.ml](https://github.com/rems-project/sail/blob/sail2/src/rewrites.ml) defines a list of rewrites:

```OCaml
let all_rewrites = [
    ("pat_string_append", Basic_rewriter rewrite_defs_pat_string_append);
    ("mono_rewrites", Basic_rewriter mono_rewrites);
    ("toplevel_nexps", Basic_rewriter rewrite_toplevel_nexps);
    ("monomorphise", Basic_rewriter monomorphise);
    ...
```

and each target specifies a list of rewrites to apply like so:

```OCaml
let rewrites_interpreter = [
    ("no_effect_check", []);
    ("realise_mappings", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("undefined", [Bool_arg false]);
    ("vector_concat_assignments", []);
    ("tuple_assignments", []);
    ("simple_assignments", [])
  ]
```

Once these rewrites have occurred the `Sail.target` function is called
which invokes the backend for each target, e.g. for OCaml:

```OCaml
  | Some "ocaml" ->
     let ocaml_generator_info =
       match !opt_ocaml_generators with
       | [] -> None
       | _ -> Some (Ocaml_backend.orig_types_for_ocaml_generator ast, !opt_ocaml_generators)
     in
     let out = match !opt_file_out with None -> "out" | Some s -> s in
     Ocaml_backend.ocaml_compile out ast ocaml_generator_info
```

There is also a `Sail.prover_regstate` function that allows the
register state to be set up in a prover-agnostic way for each of the
theorem-prover targets.

## Type Checker

The Sail type-checker is contained within
[src/type_check.ml](https://github.com/rems-project/sail/blob/sail2/src/type_check.ml). This
file is long, but is structured as follows:

1. The type checking environment is defined. The functions that
   operate on the typing environment are contained with a separate
   `Env` module. The purpose of this module is to hide the internal
   representation of the typing environment and ensure that the main
   type-checker code can only interact with it using the functions
   defined in this module, which can be set up to guarantee any
   invariant we need. Code outside the type-checker itself can only
   interact with an even more restricted subset of these functions
   exported via the mli interface file.

2. Helper definitions for subtyping and constraint solving are set
   up. The code that actually talks to an external SMT solver is
   contained within a separate file
   [src/constraint.ml](https://github.com/rems-project/sail/blob/sail2/src/constraint.ml),
   whereas the code here sets up the interface between the typing
   environment and the solver.

3. Next comes the definitions for unification and instantiation of
   types. There is some additional code (3.5) to handle subtyping with
   existential types, which can use unification to instantiate
   existentially quantified type variables.

4. Sail allows some type-level constructs to appear in term-level
   variables, but these are then eliminated during type-checking in a
   process called *sizeof*-rewriting, after the (somewhat-awkwardly)
   named *sizeof* keyword.

5. Finally all the typing rules are given. Sail has a bi-directional
   type-checking approach. So there are checking rules like
   `check_exp`, `check_pat`, etc., as well as inference rules like
   `infer_exp`, `infer_pat`, etc.

6. Effects added by the previous typing rules are now propagated
   upwards through the AST

7. Finally we have rules for checking and processing toplevel
   definitions of functions and datatypes.

The interface by which the rest of Sail can interact with the
type-checker and type annotations is strictly controlled by its [mli
interface](https://github.com/rems-project/sail/blob/sail2/src/type_check.mli)
file. We try to keep much of the type-checking internals as abstract
as possible.

## Rewriter

The rewriting framework used by the various rewrites mentioned
previously is defined in
[src/rewriter.ml](https://github.com/rems-project/sail/blob/sail2/src/rewriter.ml). It
contains various large structs with functions for every single AST
node, and allows data to be threaded through each re-write in various
ways. Most of the re-writes are defined in
[src/rewrites.ml](https://github.com/rems-project/sail/blob/sail2/src/rewrites.ml),
although the re-writer is used for other rewrite like passes such as
e.g. constant folding in
[src/constant_fold.ml](https://github.com/rems-project/sail/blob/sail2/src/constant_fold.ml)
which combines the rewriter with the Sail interpreter.

The rewriter also acts as the interface to the Sail monomorphisation
code, in
[src/monomorphise.ml](https://github.com/rems-project/sail/blob/sail2/src/monomorphise.ml).

## Jib

The C and SMT backends for Sail use a custom intermediate
representation (IR) called *Jib* (it's a type of Sail). Like the full
AST this is defined as an ott grammar in
[language/jib.ott](https://github.com/rems-project/sail/blob/sail2/language/jib.ott). The
sail "-ir" target allows Sail to be converted into this IR without any further processing.

The Jib related files are contained within a sub-directory
`src/jib/`. First we convert Sail to A-normal form (ANF) in
[src/jib/anf.ml](https://github.com/rems-project/sail/blob/sail2/src/jib/anf.ml),
then
[src/jib/jib_compile.ml](https://github.com/rems-project/sail/blob/sail2/src/jib/jib_compile.ml)
converts this into Jib.

The Jib representation has the advantage of being much simpler than
the full Sail AST, and it removes a lot of the typing complexity, as
types are replaced with simpler ones (`ctyp`). Note that many
Jib-related types are prefixed by `c` as it was originally only used
when generating C.

The key optimisation we do when generating Jib is we analyse the Sail
types using SMT to try to fit arbitrary-precision types into smaller
fixed-precision machine-word types that exist within Jib. To aid in
this we have a
[specialisation pass](https://github.com/rems-project/sail/blob/sail2/src/specialize.ml)
that removes polymorphism by creating specialised copies of functions
based on how their type-quantifiers are instantiated. This can be used
in addition to the Sail monomorphisation above.

Once we have generated Jib, the code generator from Jib into C is
fairly straightforward.

## Jib to SMT translation

Starting with some Sail such as:
```
default order dec

$include <prelude.sail>

register r : bits(32)

$property
function property(xs: bits(32)) -> bool = {
  ys : bits(32) = 0x1234_5678;
  if (r[0] == bitzero) then {
    ys = 0xffff_ffff
  } else {
    ys = 0x0000_0000
  };
  (ys == sail_zeros(32) | ys == sail_ones(32))
}
```

We first compile to Jib, then inline all functions and flatten the
resulting code into a list of instructions as below. The Sail->Jib
step can be parameterised in a few ways so it differs slightly to when
we compile Sail to C. First, a specialisation pass specialises
integer-polymorphic functions and builtins, which is reflected in the
name mangling scheme so, e.g.
```
zz7mzJzK0zCz0z7nzJzK32#bitvector_access
```
is a specialised version of bitvector access for 'n => 32 & 'm => 0.
This lets us generate optimal SMT operations for monomorphic code, as
the SMTLIB operations like ZeroExtend and Extract are only defined for
natural number constants and bitvectors of known lengths. We also have
to treat zero-length bitvectors differently to C, as SMT does not
allow zero-length bitvectors, and unlike when we compile to C, we can
have fixed-precision bitvectors of greater that 64-bits in the
generated Jib.

```
var ys#u12_l#9 : fbits(32, dec)
ys#u12_l#9 : fbits(32, dec) = UINT64_C(0x12345678)
var gs#2#u12_l#15 : bool
var gs#1#u12_l#17 : bit
gs#1#u12_l#17 : bit = zz7mzJzK0zCz0z7nzJzK32#bitvector_access(R, 0l)
gs#2#u12_l#15 : bool = eq_bit(gs#1#u12_l#17, UINT64_C(0))
kill gs#1#u12_l#17 : bit
var gs#6#u12_l#16 : unit
jump gs#2#u12_l#15 then_13
ys#u12_l#9 : fbits(32, dec) = UINT64_C(0x00000000)
gs#6#u12_l#16 : unit = UNIT
goto endif_14
then_13:
ys#u12_l#9 : fbits(32, dec) = UINT64_C(0xFFFFFFFF)
gs#6#u12_l#16 : unit = UNIT
endif_14:
kill gs#2#u12_l#15 : bool
var gs#5#u12_l#10 : bool
var gs#3#u12_l#14 : fbits(32, dec)
gs#3#u12_l#14 : fbits(32, dec) = zz7nzJzK32#sail_zeros(32l)
gs#5#u12_l#10 : bool = zz7nzJzK32#eq_bits(ys#u12_l#9, gs#3#u12_l#14)
kill gs#3#u12_l#14 : fbits(32, dec)
var gs#7#u12_l#11 : bool
jump gs#5#u12_l#10 then_11
var gs#4#u12_l#12 : fbits(32, dec)
var gs#0#u9_l#13 : fbits(32, dec)
gs#0#u9_l#13 : fbits(32, dec) = zz7nzJzK32#sail_zeros(32l)
gs#4#u12_l#12 : fbits(32, dec) = zz7nzJzK32#not_vec(gs#0#u9_l#13)
kill gs#0#u9_l#13 : fbits(32, dec)
goto end_inline_10
end_inline_10:
gs#7#u12_l#11 : bool = zz7nzJzK32#eq_bits(ys#u12_l#9, gs#4#u12_l#12)
kill gs#4#u12_l#12 : fbits(32, dec)
goto endif_12
then_11:
gs#7#u12_l#11 : bool = true
endif_12:
return : bool = gs#7#u12_l#11
kill gs#5#u12_l#10 : bool
kill ys#u12_l#9 : fbits(32, dec)
end
undefined bool
```

The above Jib is then turned into a control-flow-graph in SSA
form.

![SSA graph](https://github.com/rems-project/sail/blob/sail2/doc/sail-smt.png)

The conditionals that affect control-flow are put into separate nodes
(in yellow), so we can easily compute the global path conditional for
each block (stored in a function pi(cond0, ... , condn) by using the
yellow conditional nodes between each node and the start node.

From this form the conversion to SMT is as follows:

A variable declaration such as
```
var x : fbits(32, dec)
```
would become
```
(declare-const x (BitVec 32))
```

A call to a builtin
```
x : T = f(y0, ... , yn)
```
would become
```
(define-const x T' exp)
```
where exp encodes the builtin f using SMT bitvector operations

Phi functions are mapped to muxers as follows - for a function
`phi(x0,...,xn)` we turn that into an if-then-else statement which
selects `x0` to `xn` based on the global path conditionals of the
parent blocks corresponding to each argument. Each phi function in a
block always has the same number of arguments as the number of parent
nodes, and the arguments are in the same order as the node index for
each parent.

The above scheme generates a lot of declare-const and define-const
statements that may not be needed so we do some simple dead-code
elimination and constant propagation, which results in the following
SMT:
```
(set-logic QF_AUFBVDT)
(declare-const zR/0 (_ BitVec 32))
(define-const zysz3u12_lz30/5 (_ BitVec 32) (ite (not (= ((_ extract 0 0) zR/0) #b0)) #x00000000 #xFFFFFFFF))
(assert (and (not (ite (not (= zysz3u12_lz30/5 #x00000000)) (= zysz3u12_lz30/5 (bvnot #x00000000)) true))))
(check-sat)
```

For monomorphic-bitvector manipulating code we can generate very
compact SMT. Both specialisation and monomorphisation can be used to
help monomorphise bitvectors. For variable-length bitvectors we can
represent them as length-bitvector pairs, up to a certain bounded max
length (default 256). This is less efficient but unavoidable in
certain places. Integers are currently mapped to either 128 bit
bitvectors (or any configurable max length) or 64 bit bitvectors.

The one slightly tricky thing to support is register references, e.g.
```
(*r) : T = 0xFFFF_FFFF
```
where `r` is a register reference. For this we look for all registers
with type T (as a Jib type, where type-equality is trivial), and
convert the above to
```
if r = ref R1 then
  R1 = 0xFFFF_FFFF
else if r = ref R2 then
  R2 = 0xFFFF_FFFF
else ...
```
if we did some smarter constant folding (e.g. propagating the GPRs
letbinding in some of our specs) this could potentially generate SMT
that is just as good as a manual if-then-else implementation of the
register read/write functions. This step is done before converting to
SSA so each register in the if-then-else cascade gets the correct
indices.
