||| Two types and a constant, three concepts: what an importer takes from
||| a module is one of them, never a single constructor.
module Heap.Header

%default total

||| An object's header: a concept with its constructors, its `Show`, and
||| `size`, which is about it.
public export
data Header = Con Nat | Str Nat | Dbl

export
Show Header where
  show (Con n) = "con " ++ show n
  show (Str n) = "str " ++ show n
  show Dbl = "dbl"

||| The words an object with the header takes.
export
size : Header -> Nat
size (Con n) = S n
size (Str n) = S (S n)
size Dbl = 2

||| A part of a header: a second concept, with `place`.
public export
data Part = Tag | Count

||| Where a part sits in the header word.
export
place : Part -> Nat
place Tag = 0
place Count = 8

||| About neither type: a concept of its own.
export
wordBits : Nat
wordBits = 64
