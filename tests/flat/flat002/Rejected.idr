module Rejected

-- Each flat function here has an argument or a result that is not flat,
-- and is rejected with the reason, which the comment above it gives.
-- Compiling the program reports every one.

record Labelled where
  constructor MkLabelled
  label : String
  value : Bits64

data Box : Type where
  MkBox : {0 t : Type} -> t -> Box

-- its argument n has type Nat: Nat is an Integer at run time
%cg native flat Rejected.nat
nat : (n : Nat) -> Bits64
nat _ = 0

-- has type String: String lives on the heap
%cg native flat Rejected.str
str : String -> Bits64
str _ = 0

-- has type Integer: an Integer may need the heap
%cg native flat Rejected.int
int : Integer -> Bits64
int _ = 0

-- has type List Bits64: List is recursive
%cg native flat Rejected.list
list : List Bits64 -> Bits64
list _ = 0

-- has type Lazy Bits64: a lazy value is not flat
%cg native flat Rejected.later
later : Lazy Bits64 -> Bits64
later x = x

-- its argument a has type Type: a type at run time is not flat
%cg native flat Rejected.runtimeType
runtimeType : (a : Type) -> Bits64
runtimeType _ = 0

-- has type Labelled: the field label of MkLabelled has type String, and String lives on the heap
%cg native flat Rejected.labelled
labelled : Labelled -> Bits64
labelled _ = 0

-- its result has type List Bits64
%cg native flat Rejected.result
result : Bits64 -> List Bits64
result _ = []

-- its argument number 2 has type String
%cg native flat Rejected.unnamed
unnamed : Bits64 -> String -> Bits64
unnamed x _ = x

-- the type of a field of MkBox is not determined by the type's arguments
%cg native flat Rejected.boxed
boxed : Box -> Bits64
boxed _ = 0

-- has type AnyPtr: AnyPtr is an external type
%cg native flat Rejected.pointer
pointer : AnyPtr -> Bits64
pointer _ = 0

-- Positions count the explicit arguments only.
-- its argument number 2 has type String
%cg native flat Rejected.afterImplicit
afterImplicit : {0 n : Nat} -> Bits64 -> String -> Bits64
afterImplicit x _ = x

-- The result unfolds into the field's function once; met again, `Stream` is
-- judged as a value, and its declaration mentions it.
record Stream where
  constructor MkStream
  next : Bits64 -> Stream

-- its result has type Stream: Stream is recursive
%cg native flat Rejected.stream
stream : Stream
stream = MkStream (const stream)

-- A record that holds itself, directly or through another.
record Loop where
  constructor MkLoop
  here : Bits64
  next : Loop

-- has type Loop: Loop is recursive
%cg native flat Rejected.loop
loop : Loop -> Bits64
loop l = l.here

mutual
  record Ping where
    constructor MkPing
    pong : Pong

  record Pong where
    constructor MkPong
    ping : Ping

-- has type Ping: Ping is recursive
%cg native flat Rejected.ping
ping : Ping -> Bits64
ping _ = 0

-- A sum whose constructors are all flat, inside a recursive one.
data Tree = Leaf (Maybe Bits64) | Node Tree Tree

-- has type Tree: Tree is recursive
%cg native flat Rejected.tree
tree : Tree -> Bits64
tree _ = 0

-- A function argument is judged by its own signature, which names the
-- position that is not flat.
-- its argument number 1 has type String -> Bits64: the function's argument number 1 has type String
%cg native flat Rejected.onStrings
onStrings : (String -> Bits64) -> Bits64
onStrings f = f "x"

-- and inside a function argument's own function argument
%cg native flat Rejected.nested
nested : ((Bits64 -> String) -> Bits64) -> Bits64
nested g = 0

main : IO ()
main = pure ()
