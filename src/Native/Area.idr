||| The memory areas the runtime keeps outside the heap (`Area`), and what
||| generated code and the runtime agree on of them: the words of the
||| runtime's state (`runtimeWords`), where the root buffer holds an entry
||| (`rootOffset`), and where a top-level constant's cell is
||| (`constantOffset`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is), and like it of
||| neither: the code generator sizes and lays the areas out, in the image's
||| bss, and reaches them by their symbols; the runtime reaches them by the
||| inline externs that give their addresses. It imports nothing, so that
||| the runtime's own Idris can import it.
module Native.Area

%default total

||| The memory areas the runtime keeps outside the heap: each thread's, but
||| for the program's constants. None of them holds objects; the root buffer
||| and the constants hold values, which the collector forwards.
public export
data Area
  = ||| Arguments beyond the target's argument registers, so that no
    ||| argument travels on the machine stack and a tail call of any arity is
    ||| a move of arguments and a jump.
    ARGS
  | ||| The root buffer. Wherever a collection can start, the rendering's
    ||| stub stores the live GC-visible values here, makes the call, and
    ||| reloads them, since they may have moved. The collector reads the
    ||| entries as roots and rewrites the ones it moves. A stub pushes its
    ||| entries above those in use, so the buffer is a stack, and `NROOTS` is
    ||| its top; since only the allocation slow paths of generated code
    ||| collect, at most one stub is active at a time.
    ROOTS
  | ||| The number of entries of `ROOTS` in use.
    NROOTS
  | ||| Extra registers for register allocation; see `Slot`.
    SCRATCH
  | ||| The lowest the machine stack pointer may go in direct code, which
    ||| every direct function checks on entry. Set at start-up.
    STACK_LIMIT
  | ||| The stack pointer at the program's entry, where the system put the
    ||| argument count, the arguments' addresses and the environment's. Set
    ||| at start-up.
    ARGV
  | ||| The runtime's state: the spaces, the limits, what the last collection
    ||| left live. `runtimeWords` words, which the runtime library lays out.
    RUNTIME
  | ||| The program's top-level constants, each evaluated on its first use
    ||| and kept: a cell of two words each, 1 once the constant is evaluated,
    ||| 0 before, and then its value, which the collector forwards. As many
    ||| cells as the program has constants, which the code generator counts.
    CONSTANTS

||| The words of `RUNTIME`. The runtime's state names each of its words
||| with a proof that the area holds it.
public export
runtimeWords : Bits64
runtimeWords = 32

||| The bytes of an entry of `ROOTS`, as the power of two they are: an entry
||| is a word.
public export
rootShift : Bits64
rootShift = 3

||| Where `ROOTS` holds its entry `i`, in bytes from its start: the entries
||| in order from the start, `2 ^ rootShift` bytes each. Inline, so that a
||| flat function computes it where it uses it.
public export %inline
rootOffset : (i : Bits64) -> Bits64
rootOffset i = prim__shl_Bits64 i rootShift

||| The bytes of a cell of `CONSTANTS`, as the power of two they are: two
||| words, whether the constant is evaluated, then its value.
public export
cellShift : Bits64
cellShift = 4

||| Where `CONSTANTS` holds constant `i`'s cell, in bytes from its start:
||| the cells in order from the start, `2 ^ cellShift` bytes each.
public export %inline
constantOffset : (i : Bits64) -> Bits64
constantOffset i = prim__shl_Bits64 i cellShift
