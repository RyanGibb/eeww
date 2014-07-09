Sexplib - S-Expressions with Type Converters for OCaml
======================================================

---------------------------------------------------------------------------

What is Sexplib?
----------------

This [OCaml](http://www.ocaml.org) library contains functionality for
parsing and pretty-printing S-expressions.  In addition to that it contains a
preprocessing module for Camlp4 which can be used to automatically generate
code from type definitions for efficiently converting OCaml-values to
S-expressions and vice versa.

In combination with the parsing and pretty-printing functionality this
frees users from having to write their own I/O-routines for data structures
they define.  The tight integration with the OCaml type system also allows
for automatically verifying complex semantic properties when converting from
S-expressions to OCaml values.  Possible errors during automatic conversions
from S-expressions to OCaml-values are reported in human-readable ways
with exact location information.  The library also offers functionality for
extracting and replacing sub-expressions in S-expressions.

Usage
-----

Make sure you have installed the required `type_conv` package on your
system, too.  It should be obtainable at the same site as `sexplib`.

The API (`.mli`-files) in the `sexplib` library directory (`lib`)
is fully documented, and HTML-documentation can be built from it on
installation.  The documentation for the latest release can also be found
[online](http://mmottl.bitbucket.org/projects/sexplib/api/).

Module `Sexp` contains all I/O-functions for S-expressions, module
`Conv` helper functions for converting OCaml-values of standard types
to S-expressions.  Module `Path` supports sub-expression extraction and
substitution.

Module `syntax/pa_sexp_conv.ml` contains the extensions for the
Camlp4-preprocessor.  It adds the following three new constructs to the
language:

```ocaml
with sexp
with sexp_of
with of_sexp
```

The first one implies the last two statements.  When using these constructs
right after a type definition, function definitions will be automatically
generated which perform S-expression conversions.  For example, consider
the following type definition:

```ocaml
type t = A | B with sexp
```

The above will generate the functions `sexp_of_t` and `t_of_sexp`.
The preprocessor also supports automatic addition of conversion functions
to signatures.  Just add "`with sexp`" to the type in a signature, and the
appropriate function signatures will be generated.

Converters for standard types (`int`, `list`, `Hashtbl.t`, etc.) become
visible to the macro-generated code by opening the standard module before
their first use in a type definition.  Users will therefore usually want to
place the following at the top of their files:

```ocaml
open Sexplib.Std
```

See the file `lib_test/conv_test.ml` for an example application.  It also
demonstrates how to extract and substitute sub-expressions.

### Compiling and linking

To compile a file you will have to add preprocessing flags to the compiler
invocation.  For example for file `foo.ml`:

```sh
ocamlc -pp "camlp4o -I {path to type_conv} \
  -I {path to sexplib} pa_type_conv.cmo pa_sexp_conv.cmo" \
  -I {path to sexplib} foo.ml
```

If you are using [OCamlMakefile](http://bitbucket.org/mmottl/ocaml-makefile),
just put the following line at the top of the file, assuming you have installed
both `type_conv` and `sexplib` with ocamlfind.  The comment must start at
the beginning of the line, and you must not break lines (here broken for
readability only):

```ocaml
(*pp camlp4o -I `ocamlfind query type_conv` \
  -I `ocamlfind query sexplib` \
  pa_type_conv.cmo pa_sexp_conv.cmo *)
```

In the linking stage you will only have to link with `sexplib`.  E.g. when
using `OCamlMakefile`, just add `sexplib` to the `PACKS`-variable.

Users of the OCaml tool
[findlib](http://projects.camlcity.org/projects/findlib.html) for compiling
and linking OCaml files have an easier time: they just need to add `sexplib`
to the list of packages to make S-expression functionality available.
Adding `sexplib.syntax`, too, will make sure that files that use the type
conversion feature will be preprocessed correctly.

You may choose to place the macro `TYPE_CONV_PATH`, which takes a string
argument, at the top of files to be preprocessed if you want to force a
particular module path for error messages generated by `sexplib`.  This may
become necessary if modules are packed into a library at a later stage and
if error messages generated by Sexplib need to refer to this location to
help pinpoint the associated type.

Syntax Specification of S-expressions
-------------------------------------

### Lexical conventions of S-expression

Whitespace, which consists of space, newline, horizontal tab, and form feed,
is ignored unless within an OCaml-string, where it is treated according
to OCaml-conventions.  The left parenthesis opens a new list, the right one
closes it again.  Lists can be empty.  The double quote denotes the beginning
and end of a string following the lexical conventions of OCaml (see the
[OCaml-manual](http://www.ocaml.org/pub/docs/manual-ocaml) for details).
All characters other than double quotes, left- and right parentheses,
whitespace, carriage return, and comment-introducing characters or sequences
(see next paragraph) are considered part of a contiguous string.

A line comment is introduced using a semicolon, which comments out all
text up to the end of the next newline character.  The sequence "`%;`"
introduces an S-expression comment.  This means that the next S-expression,
which must be syntactically correct and may be an atom (quoted or unquoted)
or list, following this two-character sequence will be ignored.  Whitespace
or other comments between this sequence and the subsequent S-expression
are ignored.  Block comments are opened with "`#|`" and closed with "`|#`".
They can be nested and require that double-quotes within the block balance
and contain syntactically correct OCaml-strings, similar to quoted atoms.
These OCaml-strings may contain comment characters without causing parsing
problems.

### Grammar of S-expressions

S-expressions are either strings (= atoms) or lists.  The lists can
recursively contain further S-expressions or be empty, and must be balanced,
i.e. parentheses must match.

### Examples

```scheme
this_is_an_atom_123'&^%!  ; this is a comment
"another atom in an OCaml-string \"string in a string\" \123"

; empty list follows below
()

; a more complex example
(
  (
    list in a list  ; comment within a list
    (list in a list in a list)
    42 is the answer to all questions
    %; (this S-expression
         (has been commented out)
       )
    #| Block comments #| can be "nested" |# |#
  )
)
```

### Conversion of basic OCaml-values

Basic OCaml-values like the unit-value, integers (in all representations),
floats, strings, and booleans are represented in S-expression syntax the
same way as in OCaml.  Strings may also appear without quotes if this does
not clash with the lexical conventions for S-expressions.

### Conversion of OCaml-tuples

OCaml-tuples are simple lists of values in the same order as in the tuple.
E.g. (OCaml representation followed by S-expression after arrow):

```ocaml
(3.14, "foo", "bar bla", 27)  <===>  (3.14 foo "bar bla" 27)
```

### Conversion of OCaml-records

OCaml-records are represented as lists of pairs in S-expression syntax.
Each pair consists of the name of the record field (first element), and its
value (second element).  E.g.:

```ocaml
{
  foo = 3;
  bar = "some string";
}
<===>
(
  (foo 3)
  (bar "some string")
)
```

Type specifications of records allow the use of a special type `sexp_option`
which indicates that a record field should be optional.  E.g.:

```ocaml
type t =
  {
    x : int option;
    y : int sexp_option;
  } with sexp
```

The type `sexp_option` is equivalent to ordinary options, but is treated
specially by the code generator.  The above would lead to the following
equivalences of values and S-expressions:

```ocaml
{
  x = Some 1;
  y = Some 2;
}
<===>
(
  (x (some 1))
  (y 2)
)
```

And:

```ocaml
{
  x = None;
  y = None;
}
<===>
(
  (x none)
)
```

  Note how `sexp_option` allows you to leave away record fields that should
default to `None`.  It is also unnecessary (and actually wrong) now to write
down such a value as an option, i.e. the `some`-tag must be dropped if the
field should be defined.

The types `sexp_list`, `sexp_array`, and `sexp_bool` can be used in ways
similar to the type `sexp_option`.  They assume the empty list, empty array,
and false value respectively as default values.

More complex default values can be specified explicitly using several
constructs, e.g.:

```ocaml
let z_test v = v > 42

type t =
  {
    x : int with default(42);
    y : int with default(3), sexp_drop_default;
    z : int with default(3), sexp_drop_if(z_test);
  } with sexp
```

The `default` record field extension above is supported by the underlying
preprocessor library `type_conv` and specifies the intended default value for
a record field in its argument.  Sexplib will use this information to generate
code which will set this record field to the default value if an S-expression
omits this field.  If a record is converted to an S-expression, record fields
with default values will be emitted as usual.  Specifying `sexp_drop_default`
will add a test for polymorphic equality to the generated code such that a
record field containing its default value will be suppressed in the resulting
S-expression.  This option requires the presence of a default value.

`sexp_drop_if` on the other hand does not require a default.  Its argument
must be a function, which will receive the current record value.  If the
result of this function is `true`, then the record field will be suppressed
in the resulting S-expression.

The above extensions can be quite creatively used together with manifest
types, functors, and first-class modules to make the emission of record
fields or the definition of their default values configurable at runtime.

### Conversion of sum types

Constant constructors in sum types are represented as strings.  Constructors
with arguments are represented as lists, the first element being the
constructor name, the rest being its arguments.  Constructors may also
be started in lowercase in S-expressions, but will always be converted to
uppercase when converting from OCaml-values.

For example:

```ocaml
type t = A | B of int * float * t with sexp

B (42, 3.14, B (-1, 2.72, A))  <===>  (B 42 3.14 (B -1 2.72 A))
```

The above example also demonstrates recursion in data structures.

### Conversion of variant types

The conversion of polymorphic variants is almost the same as with sum types.
The notable difference is that variant constructors must always start with
an either lower- or uppercase character, matching the way it was specified
in the type definition.  This is because OCaml also distinguishes between
upper- and lowercase variant constructors.  Note that type specifications
containing unions of variant types are also supported by the S-expression
converter, for example as in:

```ocaml
type ab = [ `A | `B ] with sexp
type cd = [ `C | `D ] with sexp
type abcd = [ ab | cd ] with sexp
```

### Conversion of OCaml-lists and arrays

OCaml-lists and arrays are straightforwardly represented as S-expression lists.

### Conversion of option types

The option type is converted like ordinary polymorphic sum types, i.e.:

```ocaml
None        <===>  none
Some value  <===>  (some value)
```

There is a deprecated version of the syntax in which values of option type
are represented as lists in S-expressions:

```ocaml
None        <===>  ()
Some value  <===>  (value)
```

Reading of the old-style S-expression syntax for option values is
only supported if the reference `Conv.read_old_option_format` is set
to `true` (currently the default, which may change).  A conversion
exception is raised otherwise.  The old format will be written only if
`Conv.write_old_option_format` is true (also currently the default).
Reading of the new format is always supported.

### Conversion of polymorphic values

There is nothing special about polymorphic values as long as there are
conversion functions for the type parameters.  E.g.:

```ocaml
type 'a t = A | B of 'a with sexp
type foo = int t with sexp
```

In the above case the conversion functions will behave as if `foo` had been
defined as a monomorphic version of `t` with `'a` replaced by `int` on the
right hand side.

If a data structure is indeed polymorphic and you want to convert it, you will
have to supply the conversion functions for the type parameters at runtime.
If you wanted to convert a value of type `'a t` as in the above example,
you would have to write something like this:

```ocaml
sexp_of_t sexp_of_a v
```

where `sexp_of_a`, which may also be named differently in this particular
case, is a function that converts values of type `'a` to an S-expression.
Types with more than one parameter require passing conversion functions for
those parameters in the order of their appearance on the left hand side of
the type definition.


### Conversion of abstract data types

If you want to convert an abstract data type to an S-expression, you will
have to roll your own conversion functions, which should produce or accept
values of type `Sexp.t`.  If you want to make use of your abstract type
within definitions of other types, make sure that you call your conversion
function appropriately: it should be in the same scope as the typename,
and must be named `sexp_of_{typename}`.

It is possible to make use of internal representations, too, of course.
In that case you may need to shadow the generated `*_of_sexp` function with a
version that calls the generated one, but performs required semantic checks
on the resulting value to guarantee that it does not violate properties of
the abstract data type.  For example:

```ocaml
type pos_int = int with sexp

let pos_int_of_sexp sexp =
  let n = pos_int_of_sexp sexp in
  if n >= 0 then n
  else raise (Of_sexp_error (Failure "pos_int: number not positive", sexp))
```

A nice perk of `sexplib` is that using the `Of_sexp_error`-exception
will allow you to accurately pinpoint type errors in large S-expressions.
The file loading functions described further below will exploit this feature.

### Conversion of hash tables

Hash tables, which are abstract values in OCaml, are represented as association
lists, i.e. lists of key-value pairs, e.g.:

```scheme
((foo 42) (bar 3))
```

Reading in the above S-expression as hash table mapping strings to integers
(`(string, int) Hashtbl.t`) will map `foo` to `42` and `bar` to `3`.

Note that the order of elements in the list may matter, because the
OCaml-implementation of hash tables keeps duplicates.  Bindings will be
inserted into the hash table in the order of appearance.  Therefore, the
last binding of a key will be the "visible" one, the others are "hidden".
See the OCaml-documentation on hash tables for details.

Note, too, that polymorphic equality may not hold between conversions.
You will have to use a function implementing logical equality for that purpose.

### Conversion of opaque values

Opaque values are ones for which we do not want to perform conversions.
This may be, because we do not have S-expression converters for them, or
because we do not want to apply them in a particular type context. e.g. to
hide large, unimportant parts of configurations.  To prevent the preprocessor
from generating calls to converters, simply apply the qualifier `sexp_opaque`
as if it were a type constructor, e.g.:

```ocaml
type foo = int * stuff sexp_opaque with sexp
```

Thus, there is no need to specify converters for type `stuff`, and if there
are any, they will not be used in this particular context.  Needless to say,
it is not possible to convert such an S-expression back to the original value.
Here is an example conversion:

```ocaml
(42, some_stuff)  ===>  (42 <opaque>)
```

### Conversion of exceptions

S-expression converters for exceptions can be automatically registered using
the "`with sexp`" macro, e.g.:

```ocaml
module M = struct
  exception Foo of int with sexp
end
```

Such exceptions will be translated in a similar way as sum types, but their
constructor will be prefixed with the fully qualified module path (here:
`M.Foo`) so as to be able to discriminate between them without problems.

The user can then easily convert an exception matching the above one to
an S-expression using `sexp_of_exn`.  User-defined conversion functions
can be registered, too, by calling `add_exn_converter`.  This should make
it very convenient for users to catch arbitrary exceptions escaping their
program and pretty-printing them, including all arguments, as S-expressions.
The library already contains mappings for all known exceptions that can
escape functions in the OCaml standard library.

I/O and Type Conversions
------------------------

There are multiple ways of performing I/O with S-expressions.  If exact
error locations are required when type conversions fail, S-expressions need
to be parsed with location annotations.  The associated parser is slower,
however, and needs more memory.  In most cases users may therefore want to
use functions like `load_sexp_conv` or `load_sexp_conv_exn`, which load
S-expressions from files and convert them.  They initially read the file
without location annotations for performance reasons.  Only if conversions
fail, the file will be reparsed with location annotations.  Type errors
can then be reported accurately with file name, line number, column, and
file position.

---------------------------------------------------------------------------

Contact Information and Contributing
------------------------------------

In the case of bugs, feature requests, contributions and similar, please
contact the maintainers:

  * Jane Street Capital, LLC <opensource@janestreet.com>

Up-to-date information should be available at:
* <https://github.com/janestreet/sexplib>
* <https://bitbucket.org/janestreet/sexplib>
