# Idris2.Native

Idris 2 with a native code generator: `--cg native` compiles a program to a
static x86-64 Linux executable, with no C compiler, no assembler and no
linker. The code generator writes the ELF image itself.

**The executable has zero dependencies, not even libc.** It has no
interpreter, no dynamic section and no shared library to load: `ldd` calls
it "not a dynamic executable". Everything it runs is in the image, the
runtime included, and it speaks to the kernel by system calls alone. Copy
it to any x86-64 Linux machine and it runs as it is.

`idris2-native` is the Idris 2 compiler of the `Idris2` submodule, unchanged,
with this code generator added through Idris's API, the way any external
code generator is. Without `--cg`, it compiles as `idris2` does.

## Where it stands

**Self-hosted** (tag `v0.0`). `idris2-native`, compiled by itself with
`--cg native`, builds itself again from no TTCs, all 108 modules and the
image, and the image it makes is byte-identical to the one it was built
with, and to the one the Chez-built compiler makes of the same sources
(60.6 MB). The whole Idris 2 compiler, its Prelude, `base`, `contrib` and
API package, runs as native code.

**No C anywhere.** The runtime is written in Idris itself, as flat
functions (below) that the same code generator compiles: the collector,
the allocator, Integer arithmetic, doubles' text, strings, and the system
interface. A layer of system calls stands where a C library would, and is
replaceable as one.

**What a program can use:**

- All of ordinary Idris: closures, interfaces, mutual recursion, tail
  calls in constant space, type constructors as values.
- `Integer` of any size: fixnums inline, bignums by the runtime
  (schoolbook multiplication, Knuth's division, decimal text both ways,
  two's-complement bitwise operations), over machine primitives such as
  the 128-bit multiply and divide, typed with what they require and
  ensure.
- `Double` as IEEE 754 has it: arithmetic, comparisons, square roots,
  floor and ceiling; printed by the shortest digits that read back
  (Dragonbox), read correctly rounded (Clinger's fast path, then Eisel and
  Lemire's); casts to and from every integer type and `Integer`,
  correctly rounded.
- Strings in UTF-8, characters as code points; `IORef`s and buffers.
- Files, directories, file times and permissions, the environment, the
  arguments, `errno` and its messages, the standard handles.

**How it runs.** Calls are jumps: continuations are objects on the heap,
not frames on a stack, so deep recursion needs heap, not stack. The
collector is precise and copying: generated code saves its live values
where the collector finds them, and the heap grows to twice what the last
collection left live. Memory outside the heap is held by linear blocks,
and values change representation only through typed conversions, never a
cast: the linter refuses `believe_me` and its kin.

**How it is tested.** The oracle tests run each of 34 programs under
`--cg native` and under Chez and compare their output. `make selfhost`
compiles `idris2-native` natively, counts what it could not lower, and
climbs a ladder: checking modules, compiling a program and running it, and
the image the natively compiled compiler makes compared, byte for byte,
with the hosted one's.

**Not yet:**

- Speed. The natively compiled compiler builds itself in 2 h 53 min, the
  Chez-built one in 262 s: about 40 times slower. Making it faster than
  Chez is the next goal, by small iterations: half of every build today
  is the flat check loading modules it does not need.
- 87 sites in the compiler still end the program with status 70 and
  `idris: unsupported` if reached: the `crash` primitive, the
  transcendental functions of doubles, processes (`system`, `popen`),
  reading the console (`getLine`, `getChar`), the clocks, the network, and
  the evaluator that normalises terms through Chez at compile time, which
  Idris uses only on request.
- Idris's test suite run with the natively compiled compiler.
- Other targets (AArch64, other systems) and threads; the generated code
  is not optimised yet.

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
program with `%cg native`; `Native.Codegen.Native` lists them.

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

## Reading the code

The code is the reference: each module opens with what it is and how it
fits, and names the modules it works with. These are places to start.

**The code generator**, in the order a program goes through it:

- [`Native.Codegen.Native`](src/Native/Codegen/Native.idr): `--cg native`,
  the whole pipeline, and its directives.
- [`Native.Codegen.Lower`](src/Native/Codegen/Lower.idr): Idris's VMCode to
  the term IR, every function in continuation-passing style.
- [`Native.Codegen.TermIR.Program`](src/Native/Codegen/TermIR/Program.idr):
  the term IR, a typed, scoped term.
- [`Native.Codegen.RegAlloc`](src/Native/Codegen/RegAlloc.idr): the term IR
  to the [located IR](src/Native/Codegen/LocatedIR/Program.idr).
- [`Native.Codegen.X86.Render`](src/Native/Codegen/X86/Render.idr): the
  located IR as x86-64 instructions;
  [`X86.Asm`](src/Native/Codegen/X86/Asm.idr) and
  [`X86.Encode`](src/Native/Codegen/X86/Encode.idr) the instructions and
  their bytes.
- [`Native.Codegen.Link`](src/Native/Codegen/Link.idr) and
  [`Native.Codegen.ELF`](src/Native/Codegen/ELF.idr): one static executable,
  written without a linker.

**The contract** between generated code and the runtime:

- [`Native.Routine`](src/Native/Routine.idr): the runtime's routines that
  generated code calls, each by its port.
- [`Native.Port`](src/Native/Port.idr): what each register of a call
  carries.
- [`Native.Types.Kind`](src/Native/Types/Kind.idr): the heap objects and
  their layouts.
- [`Native.Primitive`](src/Native/Primitive.idr): machine operations Idris
  has no primitive for, typed with what they require and ensure.
- [`Native.Codegen.Linkage.Realised`](src/Native/Codegen/Linkage/Realised.idr):
  the contract as the loaded runtime realises it.

**Flat functions:**

- [`Native.Flat.Exp`](src/Native/Flat/Exp.idr): what the flat regime is,
  and the flat form.
- [`Native.Flat.Judgement`](src/Native/Flat/Judgement.idr): which types are
  flat, and their layouts.
- [`Native.Flat.Translate`](src/Native/Flat/Translate.idr): a definition's
  case tree to its flat form.
- [`Native.Flat.Uniform`](src/Native/Flat/Uniform.idr): the way across, to
  values as ordinary code holds them.
- [`Native.Flat.Marked`](src/Native/Flat/Marked.idr): the functions a
  program marks, and the check as each module is built.
- [`Native.Codegen.LowerFlat`](src/Native/Codegen/LowerFlat.idr): a flat
  form to a machine function.

**The runtime**, Idris compiled by the code generator above:

- [`Native.Runtime`](runtime/Native/Runtime.idr): the runtime's tiers, and
  how the code generator loads it.
- [`Native.Runtime.Start`](runtime/Native/Runtime/Start.idr): what happens
  before `main`.
- [`Native.Runtime.Ordo`](runtime/Native/Runtime/Ordo.idr): the token every
  operation of the runtime threads.
- [`Native.Runtime.Memory`](runtime/Native/Runtime/Memory.idr): addresses,
  and the only module that makes one from a word.
- [`Native.Runtime.Space`](runtime/Native/Runtime/Space.idr) and
  [`Native.Runtime.Collect`](runtime/Native/Runtime/Collect.idr): the heap,
  and Cheney's copying collector.
- [`Native.Runtime.Alloc.Allocator`](runtime/Native/Runtime/Alloc/Allocator.idr):
  memory outside the heap.
- [`Native.Support`](runtime/Native/Support.idr): the language's own values;
  [`Bignum.SignMagnitude`](runtime/Native/Support/Bignum/SignMagnitude.idr)
  for `Integer`,
  [`Double.Shortest`](runtime/Native/Support/Double/Shortest.idr) and
  [`Double.Nearest`](runtime/Native/Support/Double/Nearest.idr) for doubles'
  text, [`String.Utf8`](runtime/Native/Support/String/Utf8.idr) for strings.
- [`Native.System`](runtime/Native/System.idr): the system library, what
  stands where libc would;
  [`Native.System.Call`](runtime/Native/System/Call.idr) its system calls.

**Around it:**

- [`tests/selfhost/selfhost.sh`](tests/selfhost/selfhost.sh): how
  self-hosting is checked.
- [`tools/lint`](tools/lint/src/Lint/Main.idr): the linter, its rules and
  its refactorings.

## Tests

    make test
    make test only=native/term001
    make gate
    make selfhost

`tests/native` is the code generator's; `tests/flat` the flat regime's. The
oracle tests compare each program of `tests/native/oracle/programs` under
`--cg native` with Chez. `make gate` is what every commit passes: the tests
and the linter. `make selfhost` compiles `idris2-native` natively and
reports how far the result gets, in about a minute; it is not part of the
gate.
