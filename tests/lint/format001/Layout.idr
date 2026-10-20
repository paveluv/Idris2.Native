||| Signatures whose lines past the first start elsewhere than their type.
||| After `format`, each such line starts at the column of its type; one
||| that starts inside a bracket the signature opened before, one past the
||| bracket; one that starts with the closing bracket, at the bracket. The
||| line breaks are kept, and a line wider than the width is broken as the
||| signature's own lines are: at its type's column, not two past it.
module Layout

%default total

||| Too far left, then too far right.
export
pick : (keep : Bool) -> (first : Nat) ->
   (second : Nat) ->
         Nat
pick True a _ = a
pick False _ b = b

||| A line inside a record of named fields' braces, and the brace closing.
export
total' : {auto 0 ok : (the Nat 1 = 1,
       the Nat 2 = 2)
                } -> Nat
total' = 3

||| A data constructor's signature, and a function's in a `where` block.
public export
data Pair' : Type where
  MkPair' : (left : Nat) ->
     (right : Nat) -> Pair'

export
sumOf : Pair' -> Nat
sumOf p = go p
  where
    go : Pair' ->
           Nat
    go (MkPair' l r) = l + r

||| A line wider than the width, past the signature's first: its pieces go
||| to the type's column.
export
spread : (a : Nat) -> (b : Nat) ->
         (c : Nat) -> (d : Nat) -> (e : Nat) -> (f : Nat) -> Nat
spread a b c d e f = a + b + c + d + e + f
