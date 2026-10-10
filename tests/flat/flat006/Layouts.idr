-- The layout of each argument and of the result of a flat function: the
-- registers its values take, by its type, which the dump of the forms
-- shows. The generic function has forms at static arguments only, so none.

record Heap where
  constructor MkHeap

record Mixed where
  constructor MkMixed
  count : Bits8
  scale : Double
  token : Heap
  flag : Bool

data Shape = Circle Double | Rect Bits64 Bits64 | Empty

%cg native flat Main.word
word : Bits64 -> Char
word _ = 'a'

%cg native flat Main.double
double : Double -> Heap
double _ = MkHeap

%cg native flat Main.mixed
mixed : Mixed -> (Bits64, Bits64, Bits64)
mixed _ = (1, 2, 3)

%cg native flat Main.enum
enum : Bool -> Maybe Double
enum _ = Nothing

%cg native flat Main.shape
shape : Shape -> ()
shape _ = ()

-- A type made of the function's erased arguments is deferred.
%cg native flat Main.deferred
deferred : {0 a : Type} -> a -> Bits64
deferred _ = 0

main : IO ()
main = pure ()
