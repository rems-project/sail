Changelog
=========

Sail 0.17.1
-----------

Updated 0.17 release with bugfixes for:

* Issue 362 https://github.com/rems-project/sail/issues/362

Additionally includes patches for better ASL to Sail compatibility

Sail 0.17
---------

##### Performance improvements

This release is primarily intended to fix performance issues. Overall
the Sail to C compilation can be almost 10x faster, and consumes
significantly less memory.

##### Order parameters deprecated

The order parameter on the bitvector and vector types no longer does
anything. The `default Order <ord>` statement now sets the bitvector
and vector ordering globally. In practice only POWER uses increasing
bit order, and there is never a valid reason to mix them in a
specification. Overall they added significant complexity to the
language for no real gain. Over subsequent releases a warning will be
added before they are eventually removed from the syntax.

##### String append pattern rework

For a while string append patterns `x ^ y` have been marked with a
special non-executable effect that forbids them from being used. Now
the implementation has been removed due to the deleterious effect
the generated code has on performance. Such clauses are now eagerly
removed from the syntax tree during rewriting pending a revised
implementation.

##### SystemVerilog backend (EXPERIMENTAL)

Sail can now produce SystemVerilog output using the -sv flag. Note
that this is not intended to be human readable or produce a
synthesizable design, but is instead intended to be used with
SystemVerilog verification tools like JasperGold.

Sail 0.16
---------

##### New documentation backend

A new documentation backend for integrating with Asciidoctor has been
added.

##### Automatic formatting (EXPERIMENTAL)

The `sail -fmt` option can be used to automatically format Sail
source. This currently misses some features and can produce ugly
output in some known cases, so is not ready for serious usage yet.

##### Fixes

Various bugfixes including:

* Issue 203: https://github.com/rems-project/sail/issues/203
* Issue 202: https://github.com/rems-project/sail/issues/202
* Issue 188: https://github.com/rems-project/sail/issues/188
* Issue 187: https://github.com/rems-project/sail/issues/187
* Issue 277: https://github.com/rems-project/sail/issues/277

Various mapping issues such as:

* Issue 244: https://github.com/rems-project/sail/issues/244

As well as other minor issues

The `val cast` syntax and support for implict casts is now entirely
removed, as mentioned in the previous release changes. The flags are
still allowed (to avoid breaking Makefiles) but no longer do anything.

The pattern completeness checker has been improved and is now context
sensitive in some cases.

Sail 0.15
---------

##### More modular codebase and dune build system

The Sail internals have been refactored into separate packages for
each Sail backend (c/lem/coq and so on). The shared parts of Sail are
now contained in a separate libsail OCaml library. The main Sail
executable links together all the Sail backends into a single
executable.

With this architecture new backends can be implemented outside the
main Sail repository as _plugins_, and loaded via `sail -plugin`.

The Sail build system has been transitioned from the legacy ocamlbuild
system to dune.

This has been a significant refactoring of the core Sail codebase, and
while all efforts have been taken to ensure backwards-compatibility
and minimise any potential breakage, it is possible there exists some.

##### New pattern completeness checker

Sail now has a new pattern completeness checker that can generate
counterexamples for incomplete patterns. It is designed to be less
noisy, as it only issues warnings when it can guarantee that the
pattern is incomplete.

##### Implicit casts now forbidden by default

Previously they were only forbidden by the `-dno_cast` flag (which is
used by both sail-riscv and sail-arm). This behaviour is now the
default and this flag is ignored. The `-allow_deprecated_casts` flag
must be used to enable this now. Implicit casts will be fully removed
in the next Sail release.

##### New concurrency interface (EXPERIMENTAL)

This release contains a new way of interfacing with external
concurrency models by way of user defined effects. See
lib/concurrency_interface for an example. This is currently
experimental and not fully supported in all backends. Definition of
new effects is currently only allowed with the `$sail_internal`
directive (see below).

##### No more explicit effect annotations (DEPRECATION)

Explicit effect annotations are now deprecated and do nothing. This
change relates to the previous change to allow custom outcomes in the
event monad, as the effect system no-longer corresponded in any
meaningful way with whether functions would become monadic or not in
Sail's theorem prover backends.

Function specifications (`val` keyword) can now be marked as `pure`. If
this is done, the functions _must_ have no side-effects. The
requirements for a function to be pure in this sense are stricter than
they were previously - a pure function must not:

* Throw an exception
* Exit (either explicitly or by failing an assertion)
* Contain a possibly incomplete pattern match
* Read or write any register
* Call any impure function

This more strict notion of purity fixes some long-standing bugs when
generating theorem prover definitions from Sail.

Note that functions do not have to be explicitly marked pure to be
considered pure. Purity will be inferred automatically. The pure
annotation is used to declare primitive functions as pure, and make it
a hard error if a function is inferred to be impure.

There are two places in the language where code must be pure:

* Top level let-bindings `let x = exp`
* Loop and function termination measures

##### Stricter typechecking for mutable variables (MINOR BREAKING)

Previously Sail allowed some assignment constructions that were a bit
complex, for example one could declare a variable and modify an
existing one in the same statement, e.g.

```
x: int = 1;
(x, y: int) = (2, 3);
```

This is now forbidden, so l-expressions can either modify existing
variables or declare new ones, but never both simultaneously. This
change is primarily to increase readability, and simplify the language
internally.

In the future we may move further towards a world where new
assignments must be declared with a `var` keyword, like the `let`
keyword.

Variable declarations are now forbidden in places where their scope is
not syntactically obvious, for example:

```
val f : (unit, int) -> unit
...
f(x: int = 3, x)
```

The breakage caused by this change should be minor as we hope
well-written Sail specifications do not declare variables in this way.

##### GCC style error message formatting

Error messages are now formatted as per:

https://www.gnu.org/prep/standards/standards.html#Errors

which should allow better editor integration

##### sail_internal directive

A new directive `$sail_internal` has been introduced. When placed in a
file this allows the use of experimental or unstable functionality. It
also allows the use of various identifiers that are ordinarily
forbidden. Its primary purpose is to allow the Sail library to be
implemented using new unstable features that may change, without them
being exposed (and therefore relied upon) by downstream users.

As such, any Sail file using this directive may become broken at any
point.

Sail 0.14
---------

This is mostly a bugfix release

Sail 0.13
---------

##### Experimental new C backend

Supports creating C code that works as a library in a more natural
way. Rather than defining lots of global state, the model state will
be packaged into a `sail_state` struct that is passed into each
generated C function. The code generation is much more configurable,
including options for fine-grained control over name-mangling (see
etc/default_config.json).

Currently the -c2 option can be used. Eventually it is planned that
this will become the default C code generation option, and the old C
code generator will be removed.

##### Improved monomorphisation

The monomorphisation pass for Isabelle and HOL4 has been improved
significantly.

##### Code coverage

There is now a code coverage tool (sailcov) in the sailcov
subdirectory of this repository

Sail 0.8
--------

##### More flexible type synonym syntax

Can now define type synonyms for kinds other than `Type`. For example:
```
type xlen : Int = 64
type xlenbits = bits(xlen)
```
the syntax is
```
type <name> : <kind> = <value>
```
for synonyms with no arguments and
```
type <name>(<arguments>)[, <constraint>] -> <kind> = <value>
```
for synonyms that take arguments. Valid kinds are `Int`, `Bool`, `Ord`, and
`Type`. `: Type` or `-> Type` can be omitted.

This can be used to define constraint synonyms, e.g.
```
type is_register_index('n : Int) = 0 <= 'n <= 31
val my_function : forall 'n, is_register_index('n). int('n) -> ...
```
Type synonyms with constraints and multiple arguments can be declared as e.g.
```
type my_type('n: Int, 'm: Int), 'n > 'm > 0 = vector('n, dec, bits('m))
```

The previous syntax for numeric constants (which was never fully implemented) of
```
constant x = <value>
```
is no longer supported.

##### Emacs mode improvements

Can now use `C-c C-s` in Emacs to start a Sail interactive
sub-process, assuming `sail` is available in `$PATH`. Using `C-c C-l`
or simply saving a changed Sail file will cause it to be checked. Type
errors will be highlighted within the Emacs buffer, and can be jumped
to using `C-c C-x`, much like Merlin for OCaml. `C-c C-c` will display
the type of the expression under the cursor for a checked Sail
file. This particular is slightly experimental and won't always
display the most precise type, although Emacs will bold the region
that sail thinks is under the cursor to make this clear. The
interactive Sail session can be ended using `C-c C-q`.

To support multiple file ISA specifications, a JSON file called
sail.json can be placed in the same directory as the .sail files. It
specifies the dependency order for the .sail files and any options
required by Sail itself. As an example, the file for v8.5 is
```json
{
    "options" : "-non_lexical_flow -no_lexp_bounds_check",
    "files" : [
	"prelude.sail",
	"no_devices.sail",
	"aarch_types.sail",
	"aarch_mem.sail",
	"aarch64.sail",
	"aarch64_float.sail",
	"aarch64_vector.sail",
	"aarch32.sail",
	"aarch_decode.sail"
    ]
}
```

For this to work Sail must be build with interactive support as `make
isail`. This requires the yojson library as a new dependency (`opam
install yojson`).

##### Boolean constraints and type-variables

We now support Boolean type arguments in much the same way as numeric
type arguments. Much like the type int('n), which means an integer
equal to the type variable 'n, bool('p) now means a Boolean that is
true provided the constraint 'p holds. This enables us to do flow
typing in a less ad-hoc way, as we can now have types like
```
val operator <= : forall 'n 'm. (int('n), int('n)) -> bool('n <= 'm)
```
The main use case for this feature in specifications is to support
flags that change the range of type variables, e.g:
```
val my_op : forall 'n ('f : Bool), 0 <= 'n < 15 & ('f | 'n < 4).
  (bool('f), int('n)) -> unit

function my_op(flag, index) = {
  if flag then {
	// 0 <= 'n < 15 holds
	let x = 0xF[index]; // will fail to typecheck here
	...
  } else {
	// 0 <= 'n < 4 holds
	let x = 0xF[index]; // will typecheck here
	...
  }
}
```

This change is mostly backwards compatible, except in some cases extra
type annotations may be required when declaring mutable Boolean
variables, so
```
x = true // declaration of x
x = false // type error because x inferred to have type bool(true)
```
should become
```
x : bool = true // declaration of x
x = false // fine because x can have any Boolean value
```

##### Simpler implicit arguments

Function implicit arguments are now given explicitly in their type signatures so
```
val zero_extend : forall 'n 'm, 'm >= 'n. bits('n) -> bits('m)

function zero_extend(v) = zeros('m - length(v)) @ v
```
would now become
```
val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function zero_extend(m, v) = zeros(m - length(v)) @ v
```

This radically simplifies how we resolve such implicit arguments
during type-checking, and speeds up processing large specifications
like ARM v8.5 significantly.

There is a symbol `FEATURE_IMPLICITS` which can be used with `$ifdef`
to write both new and old-versions if desired for backwards
compatibility, as the new version is syntactically valid in older Sails,
but just doesn't typecheck.

##### Parameterised bitfields

Bitfields can now be parameterised in the following way:
```
type xlenbits = bits(xlen)

bitfield Mstatus : xlenbits = {
  SD  : xlen - ylen,
  SXL : xlen - ylen - 1 .. xlen - ylen - 3
}
```

This bitfield would then be valid for either
```
type xlen : Int = 64
type ylen : Int = 1
```
or
```
type xlen : Int = 32
type ylen : Int = 1
```

##### Lem monad embedding changes

The monad embedding for Lem has been changed to make it more friendly
for theorem proving. This can break model-specific Lem that depends on
the definitions in [src/gen_lib](src/gen_lib).
