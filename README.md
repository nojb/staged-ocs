staged-ocs - a multi-stage R5RS Scheme interpreter written in MetaOCaml
-------------------------------------------------------------------

`staged-ocs` is a *multi-stage* Scheme interpreter written in (Meta)OCaml.  This
means that instead of interpreting Scheme directly, it first *translates* the
Scheme code into OCaml at runtime and then executes that.

It is distributed under a permissive (two-clause) BSD-style license.

The rest of this file gives some information about this implementation.  Most of
the text is a direct copy or a very ligthly edited copy of the README file of
the original `ocs` (see next section).

Contact: Nicolas Ojeda Bar (<n.oje.bar@gmail.com>)

## Acknowledgements

`staged-ocs` is directly based on the `ocs` Scheme interpreter.  The original
webpage seems to have disappeared, but a version of it can be found at
<http://archive.today/dSl40>.

## General

Ocs is an implementation of Scheme, as defined by R5RS.  It is
written entirely in OCaml and can be trivially embedded in any
OCaml program.

Known deviations from R5RS:

- `transcript-on` and `transcript-off` are currently not implemented
- `scheme-report-environment` and `null-environment` ignore their
   argument
- `dynamic-wind` is not currently supported

Anything else that does not work as specified in R5RS is a bug.

## Installation

Requirements:

- GNU make
- MetaOCaml BER 101 (<http://okmij.org/ftp/ML/MetaOCaml.html>)

In order to install MetaOCaml, the easiest way is to use opam (<https://opam.ocaml.org>).

    opam switch 4.01.0+BER

Once MetaOCaml is installed, clone the git repository and type make in the `src` directory.

    git clone https://github.com/nojb/staged-ocs
    cd staged-ocs
    cd src
    make
 
This should produce a stand-alone, bytecode interpreter (`ocs_main.byte`). **See
the next section for information on how to run it.**

## The 'ocs_main.byte' command

**You need to `cd` to the `_build` subdirectory before running the
  `ocs_main.byte` executable (due to an issue related to how MetaOCaml-generated
  code works).  This problem should be solved soon.**

    cd _build
    ./ocs_main.byte [-dstaged]

Execute `ocs_main.byte` to run the interpreter in interactive mode.  If you want
to see the generated OCaml code, run `ocs_main.byte -dstaged`.

If invoked with arguments, the interpreter will read and evaluate the files
listed as arguments and exit.  The evaluation results (and the intermediate
OCaml) are not printed.

## Implementation Details

Implementing Scheme in OCaml is so straightforward that it hardly
needs any documentation.  The following mappings between languages
are done:

- Scheme is dynamically typed.  Scheme values are represented by
  the OCaml type `Ocs_types.sval`.

- In Scheme, top-level bindings are global and all variables are mutable.
  Variables references are bound through environments (`Ocs_types.env`) to
  global slots (`Ocs_types.gvar`) or frame indices (the actual frames are
  implicitly kept by the OCaml interpreter at run-time).

- Scheme has capturable, first-class continuations.  Most of the evaluator is
  written in continuation-passing style in order to allow this.

Where discussing types, the rest of this section assumes that the types defined
in the module `Ocs_types` are visible.

## Staging

Scheme values (S-expressions) are of the type `sval`.

Before evaluation Scheme values are compiled to internal representations of the
type code.  This is done by the function

    Ocs_compile.compile : env -> sval -> scode

The env type is used during compilation for variable bindings.  A new env is
created for each new scope and frame.  The base environment with the basic
language bindings can be created using

    Ocs_top.make_env : unit -> env

Staging is done by

    Ocs_eval.stage : senv -> thread code -> (sval code -> unit code) -> scode -> unit code

where the third argument is a continuation to pass the result to.

The `thread` type is used at run-time for storing the current input/output ports
and the current dynamic extent.  It does not represent a thread in the
concurrent sense, but rather the evaluation state, and is copied and changed
rather than modified in place.  The initial thread can be created using
`Ocs_top.make_thread : unit -> thread`.

## Continuations and I/O

Any continuations captured are associated with the thread at the time of
capture, so if a continuation is used to escape a `with-input-from-file` or
`with-output-to-file`, the input/output port is restored to those of the time of
capture.

If a continuation is used to return to a `with-input-from-file` or
`with-output-to-file`, the port is once again set to the one opened by the
`with-...-file` call.  However, if the thunk has already exited once, the port
will be closed and no longer be valid for I/O calls.

## Numbers

The full R5RS numeric tower is implemented, with the following internal
representations:

Exact numbers are

- 31- or 63-bit integers (OCaml `int`)
- `Big_int` objects from the `Num` library when unboxed integers are
  too small
- `Ratio` objects from the `Num` library for rationals

Inexact numbers are

- 64-bit IEEE floats for reals (OCaml `float`)
- Pairs of 64-bit IEEE floats for complex numbers (OCaml `Complex.t`)

Since inexact numbers are represented internally as binary floating point,
conversions to exact numbers are most precise for fractions of powers of two

    (inexact->exact 2.125) ==> 17/8

compared to

    (inexact->exact 0.3) ==> 5404319552844595/18014398509481984

And in fact many rationals will not satisfy

    (= (inexact->exact (exact->inexact r)) r)

However

    (rationalize (inexact->exact 0.3) (expt 2 -54)) ==> 3/10

