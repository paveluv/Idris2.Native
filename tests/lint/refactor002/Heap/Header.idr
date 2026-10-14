||| A header and its parts: two concepts, which `split-module` takes apart.
module Heap.Header

import Data.List

%default total

||| A part of a header.
public export
data Part = Tag | Count

||| Where a part sits in the header word.
export
place : Part -> Nat
place Tag = 0
place Count = 8

||| An object's header.
public export
data Header = Con Nat | Str Nat

||| A header's parts: what stays uses what moves, so `Heap.Header` imports
||| `Heap.Part` after the split.
export
parts : Header -> List Part
parts (Con _) = [Tag, Count]
parts (Str _) = [Tag]

||| The headers, a constructor's between each two: `Data.List`'s, which
||| `Heap.Part` takes with the other imports and `prune-imports` removes.
export
spaced : List Header -> List Header
spaced = intersperse (Con 0)
