||| The per-thread memory areas the runtime keeps outside the heap (`Area`),
||| and what generated code and the runtime agree on of them: the words of
||| the runtime's state (`runtimeWords`), and where the root buffer holds an
||| entry (`rootOffset`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Enc` says what it is), and like it of
||| neither: the code generator sizes and lays the areas out, in the image's
||| bss, and reaches them by their symbols; the runtime reaches them by the
||| inline externs that give their addresses. It imports nothing, so that
||| the runtime's own Idris can import it.
module Native.Area

%default total

||| The per-thread memory areas the runtime keeps outside the heap. None of
||| them holds objects.
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
