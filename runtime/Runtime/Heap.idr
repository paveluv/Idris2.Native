||| The token every operation on memory threads, and the shape of those
||| operations.
|||
||| The runtime has no monad and no `IO`. An operation takes the token
||| `Heap`, linearly, and returns it with its value, so the operations of a
||| routine form one sequence by data dependence: none can be dropped,
||| duplicated or reordered against another. `Heap` has one constructor and
||| no fields, so it takes no register: the ordering costs nothing at run
||| time. `do` works over the inline bind below, which unfolds into the
||| chain of `let`s it stands for.
module Runtime.Heap

%default total

||| The token.
public export
data Heap : Type where
  MkHeap : Heap

||| What an operation returns: the token, linearly, and its value.
public export
data Ret : (h : Type) -> Type -> Type where
  (#) : (1 m : h) -> (v : a) -> Ret h a

||| An operation on memory with a value of type `a`.
public export
Op : (h : Type) -> Type -> Type
Op h a = (1 m : h) -> Ret h a

public export %inline
(>>=) : Op h a -> (a -> Op h b) -> Op h b
(>>=) f g m = let (m' # v) = f m in g v m'

public export %inline
(>>) : Op h () -> Op h b -> Op h b
(>>) f g m = let (m' # _) = f m in g m'

public export %inline
pure : a -> Op h a
pure v m = m # v
