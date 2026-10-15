||| The per-thread memory areas the runtime keeps outside the heap (`Area`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Native.Codegen.IRCommon.Ty` says what it is).
module Native.Codegen.IRCommon.Area

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

||| The words of `RUNTIME`.
public export
runtimeWords : Nat
runtimeWords = 32
