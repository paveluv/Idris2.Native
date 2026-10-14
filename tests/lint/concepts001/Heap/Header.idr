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

||| Whether two headers are of one kind, whatever their sizes: enough lines
||| with the others for `Header` to be a piece worth a module of its own.
export
sameKind : Header -> Header -> Bool
sameKind (Con _) (Con _) = True
sameKind (Str _) (Str _) = True
sameKind Dbl Dbl = True
sameKind _ _ = False

||| A header with its count doubled, its kind kept.
export
doubled : Header -> Header
doubled (Con n) = Con (n + n)
doubled (Str n) = Str (n + n)
doubled Dbl = Dbl

||| A part of a header: a second concept, with `place`.
public export
data Part = Tag | Count

||| Where a part sits in the header word.
export
place : Part -> Nat
place Tag = 0
place Count = 8

||| How many bits a part takes in the header word: with `place` and
||| `wordBits`, enough lines for `Part` to be a piece worth a module.
export
width : Part -> Nat
width Tag = 8
width Count = 56

||| The part after a part in the header word, the last one first again.
export
next : Part -> Part
next Tag = Count
next Count = Tag

||| Whether a part is the header word's first.
export
first : Part -> Bool
first Tag = True
first Count = False

||| About neither type: a concept of its own.
export
wordBits : Nat
wordBits = 64
