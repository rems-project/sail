Changelog
=========

Sail 0.8
--------

###### More flexible type synonym syntax

Can now define type synonyms for kinds other than type. For example:
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

###### Emacs mode improvements

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

###### Boolean constraints and type-variables

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

###### Simpler implicit arguments

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

###### Lem monad embedding changes

The monad embedding for Lem has been changed to make it more friendly
for theorem proving. This can break model-specific Lem that depends on
the definitions in [src/gen_lib](src/gen_lib).
