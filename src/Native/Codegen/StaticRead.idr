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
||| erased value is its word; a nullary constructor and an object a maker
||| made (`Types.FromWords`) are static objects, read by their addresses.
||| Every other value is refused, with why: a constructor with fields, a
||| closure and a type, which the code generator does not lay out as static
||| data yet.
module Native.Codegen.StaticRead

import Native.Codegen.ConstantWord
import Native.Codegen.Evaluate

import Core.Name
import Core.Name.Namespace
import Core.TT.Primitive
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
  ||| A static object of the program, by its name, which holds what the
  ||| plan says: read as its address.
  Object : Name -> ConstantWord.StaticPlan -> StaticRead

||| How code reads the constant of this name marked static, from its value;
||| or why the value is not laid out as static data. The bignum encoding
||| decides whether a big `Integer` is a value at all
||| (`ConstantWord.constantWord`). A nullary constructor is the static
||| object every use of it shares; a maker's object is a `BYTES` of its
||| words, named after the constant.
export
staticRead : Types.BignumEnc -> Name -> Evaluate.Value -> Either String StaticRead
staticRead bignum n v = case v of
  Evaluate.VConst k => Literal k <$ ConstantWord.constantWord bignum k
  Evaluate.VErased => Right Erased
  Evaluate.VCon _ (Just c) [] => Right (Object (ConstantWord.nullaryCon c) (ConstantWord.Nullary c))
  Evaluate.VCon _ (Just _) (_ :: _) =>
    Left "a constructor with fields, which the code generator does not lay out as static data yet"
  Evaluate.VCon _ Nothing _ =>
    Left "a type, which the code generator does not lay out as static data yet"
  Evaluate.VBytes ws =>
    Right (Object (NS (mkNamespace "_native") (UN (Basic ("static " ++ show n))))
             (ConstantWord.Words (values ws)))
  Evaluate.VLam {} => Left (closure "a function")
  Evaluate.VPartial {} => Left (closure "a function")
  Evaluate.VDelay {} => Left (closure "a delayed value")
  where
    -- a value that ordinary code holds as a closure: a lambda, a partial
    -- application, or a delay
    closure : String -> String
    closure what = what ++ ", whose closure the code generator does not lay out as static data yet"
