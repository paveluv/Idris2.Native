# idris2-native

Idris 2 with a native code generator: `--cg native` compiles a program to a
static x86-64 Linux executable, with no C compiler, no assembler and no
linker. It is a work in progress: programs that print or read do not run yet,
and a construct the backend does not lower yet ends the program with status
70 and `idris: unsupported`.

`idris2-native` is the Idris 2 compiler of the `Idris2` submodule, unchanged,
with this code generator added through Idris's API, the way any external
code generator is. Without `--cg`, it compiles as `idris2` does.

## Building

The submodule pins the Idris 2 this code generator is written against. Its
compiler, libraries and API package are built into `build/prefix`, by any
`idris2` in `PATH` that can bootstrap it:

    git submodule update --init
    make upstream
    make

`make upstream` is needed once, and again after the pin moves. `make`
builds `build/exec/idris2-native` and installs this code generator's
modules into `build/prefix` as the package `idris2-native`.

## Using it

    build/exec/idris2-native --cg native Main.idr -o main

Directives for the code generator are given with `--directive`, or in the
program with `%cg native`; `Compiler.Native.Native` lists them.

### Flat functions

A function whose values all fit in registers, machine integers, `Char`,
`Double`, and records and sums of them that are not recursive, can be
compiled *flat*: without the heap, as a machine function. A program marks
such functions with a directive, which Idris keeps with the module, so a
library's marks reach the programs that import it:

    %cg native flat Main.sumTo

    sumTo : Bits64 -> Bits64 -> Bits64
    sumTo acc 0 = acc
    sumTo acc n = sumTo (acc + n) (n - 1)

Each name is qualified as far as it takes to name one function. Every other
code generator ignores the directive and compiles the function as usual.

Everything a flat function calls is compiled flat too, without marking:
a function whose arguments and result are flat gets a flat form of its
own, and a generic or higher-order one gets a copy for each distinct
dictionary, function or other static argument it is called with, a
lambda's captured variables passed as the copy's parameters. A flat
function may itself take function arguments whose own arguments and result
are flat; it is then copied at each call.

Each marked function is translated into its flat form (`Flat.Translate`) as
its module is built, `--check` included, and one that is not flat is
reported then, with the reason, the chain of calls that reaches it, and the
term at fault. The check is the incremental code generator `flat-check`,
which compiles nothing and which `idris2-native` adds to the ones
`IDRIS2_INC_CGS` names. Compiling a program translates the functions again,
and reports what no check reported: a name that names no function, or more
than one, and functions of modules built without the check.

`--cg flat-oracle` compiles each marked function from its flat form, made
ordinary again, with Chez: it tests the translation, since the program must
behave as it does under Chez.

## Tests

    make test
    make test only=native/term001

`tests/native` is the code generator's; `tests/flat` the flat regime's. The
oracle tests compare each program of `tests/native/oracle/programs` under
`--cg native` with Chez.
