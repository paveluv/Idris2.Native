||| The term IR's variables (`Var`): a position in a context, with an erased
||| proof of its type there.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Var

import Data.List.Quantifiers
import Data.Nat
import Decidable.Equality.Core

%default total

||| That the list has the value at the position, counted from its front.
public export
data AtIndex : Nat -> a -> List a -> Type where
  First : AtIndex Z x (x :: xs)
  Later : AtIndex n x xs -> AtIndex (S n) x (y :: xs)

||| A variable of a context: its position, with the erased proof that the
||| context has a value of the type there. At run time it is the position
||| alone.
public export
record Var (xs : List a) (x : a) where
  constructor MkVar
  index : Nat
  0 at : AtIndex index x xs

||| The variable just bound.
public export
here : Var (x :: xs) x
here = MkVar 0 First

||| A variable under one more binding.
public export
later : Var xs x -> Var (y :: xs) x
later (MkVar i at) = MkVar (S i) (Later at)

||| What an environment holds for the variable.
public export
fetch : Var xs x -> All p xs -> p x
fetch (MkVar i at) env = go i at env
  where
    go : (i : Nat) -> (0 _ : AtIndex i y ys) -> All p ys -> p y
    go Z First (z :: _) = z
    go (S i) (Later at) (_ :: zs) = go i at zs

||| The entry a variable names: a callee's signature, a static's.
public export
entry : (xs : List a) -> Var xs x -> a
entry xs (MkVar i at) = go i xs at
  where
    go : (i : Nat) -> (ys : List a) -> (0 _ : AtIndex i y ys) -> a
    go Z (z :: _) First = z
    go (S i) (_ :: zs) (Later at) = go i zs at

||| The variable at the position, if the context has the type there.
public export
varAt : DecEq a => (i : Nat) -> (x : a) -> (xs : List a) -> Maybe (Var xs x)
varAt Z x (y :: ys) = case decEq x y of
  Yes Refl => Just here
  No _ => Nothing
varAt (S i) x (_ :: ys) = map later (varAt i x ys)
varAt _ _ [] = Nothing

||| Every entry of a list with its variable, in one pass: the proofs are
||| erased, so building them costs nothing at run time.
public export
enumerate : (xs : List a) -> List (x ** Var xs x)
enumerate xs = go 0 xs (\p => p)
  where
    -- How a position in a suffix of `xs` is one in `xs`.
    0 Into : Nat -> List a -> Type
    Into i rest = {y : a} -> {j : Nat} -> AtIndex j y rest -> AtIndex (i + j) y xs

    0 step : {i : Nat} -> {0 z : a} -> {0 zs : List a} -> Into i (z :: zs) -> Into (S i) zs
    step f {y} {j} p = replace {p = \n => AtIndex n y xs} (sym (plusSuccRightSucc i j)) (f (Later p))

    go : (i : Nat) -> (rest : List a) -> (0 _ : Into i rest) -> List (x ** Var xs x)
    go i [] _ = []
    go i (y :: ys) f =
      (y ** MkVar i (replace {p = \n => AtIndex n y xs} (plusZeroRightNeutral i) (f First))) :: go (S i) ys (step f)
