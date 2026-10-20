||| The token every operation of the runtime threads (`Ordo`), and the shape
||| of those operations.
|||
||| The name is made up, from the Latin for order, sequence: what the token
||| does. It orders every effect of the machine, not the collector's heap's
||| alone: the heap, memory reached by byte address (the per-thread areas, the
||| system's arguments and environment, the memory outside the heap the
||| allocator gives), the pinned registers, and the system's services.
|||
||| The runtime has no monad and no `IO`. An operation takes the token
||| `Ordo`, linearly, and returns it with its value, so the operations of a
||| routine form one sequence by data dependence: none can be dropped,
||| duplicated or reordered against another. `Ordo` has one constructor and
||| no fields, so it takes no register: the ordering costs nothing at run
||| time. `do` works over the inline bind below, which unfolds into the
||| chain of `let`s it stands for.
module Native.Runtime.Ordo

%default total

||| The token.
public export
data Ordo : Type where
  MkOrdo : Ordo

||| What an operation returns: the token, linearly, and its value.
public export
data Ret : (h : Type) -> Type -> Type where
  (#) : (1 m : h) -> (v : a) -> Ret h a

||| An operation on memory with a value of type `a`.
public export
Op : (h : Type) -> Type -> Type
Op h a = (1 m : h) -> Ret h a

||| The bind, and the one that drops a unit: each uses its operands once,
||| and says so, so that a linear value an operation holds (a block of
||| memory, `Alloc.Block`) is used in only one of them, and `do` keeps it
||| linear across its steps.
public export %inline
(>>=) : (1 f : Op h a) -> (1 g : a -> Op h b) -> Op h b
(>>=) f g m = let (m' # v) = f m in g v m'

public export %inline
(>>) : (1 f : Op h ()) -> (1 g : Op h b) -> Op h b
(>>) f g m = let (m' # _) = f m in g m'

public export %inline
pure : a -> Op h a
pure v m = m # v

||| End the program with the message, whatever operation was expected.
export
crashOp : String -> Op h a
-- lint: allow trust-escape: a crash returns nothing, so it is an operation of any result
crashOp msg = assert_total (idris_crash msg)
