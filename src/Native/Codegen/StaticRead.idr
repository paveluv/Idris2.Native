||| How code reads a constant the program marks static (`StaticRead`),
||| whose value the code generator computed as it compiled the program
||| (`Native.Codegen.Evaluate`): with no call and no cell, as the value
||| itself, which the image holds. Ordinary code reads each so
||| (`Native.Codegen.Lower`), and flat code too where it holds the value in
||| one uniform register or as a machine scalar
||| (`Native.Codegen.LowerFlat.flatRead`).
|||
||| A number, a string or a double is read as the literal it is, which
||| code reads as it reads any literal (`ConstantWord.constantWord`); the
||| erased value is its word; every other value is a static object, read by
||| its address: a nullary constructor's, which every use of it shares, a
||| constructor with fields, and an object a maker made (`Types.FromWords`),
||| laid out with the objects they hold by one rule
||| (`Native.Codegen.ValueWord`). A type, a function and a delayed value
||| are refused, with why, as is one that holds one: the code generator
||| does not lay them out as static data yet.
module Native.Codegen.StaticRead

import Native.Codegen.ConstantWord
import Native.Codegen.Evaluate
import Native.Codegen.ValueWord

import Core.Name
import Core.TT.Primitive
import Data.List
import Data.SortedMap
import Native.Types.BignumEnc as Types

%default total

||| How code reads a constant marked static: as its value, by no call.
public export
data StaticRead : Type where
  ||| A number, a string or a double: read as the literal it is.
  Literal : Constant -> StaticRead
  ||| The erased value.
  Erased : StaticRead
  ||| A static object of the program, by its name: read as its address.
  Object : Name -> StaticRead

||| How code reads each constant marked static, of these names and values,
||| and every static object the reads name, those the objects hold among
||| them, with what each holds; or why each value that is not laid out as
||| static data is not. The values are laid out by the one rule
||| (`ValueWord.valueWord`), under the bignum encoding, in the order of the
||| constants' names, so that the objects are named alike whatever the
||| order the values are given in. A read is the literal of a constant,
||| so that code reads it as it reads the literal, or the erased value, or
||| the object the value's word names.
export
staticReads : Types.BignumEnc -> List (Name, Evaluate.Value) ->
              (List (Name, String), SortedMap Name StaticRead,
               SortedMap Name ConstantWord.StaticPlan)
staticReads bignum values =
  let (refused, reads, os) = foldl one ([], empty, ValueWord.noObjects)
                                   (sortBy (\a, b => compare (fst a) (fst b)) values) in
  (reverse refused, reads, os.plans)
  where
    -- a value's word as a read
    wordRead : ConstantWord.StaticWord -> StaticRead
    wordRead (ConstantWord.Fixnum i) = Literal (I64 i)
    wordRead ConstantWord.Erased = Erased
    wordRead (ConstantWord.Object o) = Object o

    -- one constant laid out after those before it, or refused, the
    -- objects then as they were
    one : (List (Name, String), SortedMap Name StaticRead, ValueWord.StaticObjects) ->
          (Name, Evaluate.Value) ->
          (List (Name, String), SortedMap Name StaticRead, ValueWord.StaticObjects)
    one (refused, reads, os) (n, v) = case ValueWord.valueWord bignum v os of
      Left why => ((n, why) :: refused, reads, os)
      Right (w, os') =>
        let rd = case v of
                   Evaluate.VConst k => Literal k
                   _ => wordRead w in
        (refused, insert n rd reads, os')
