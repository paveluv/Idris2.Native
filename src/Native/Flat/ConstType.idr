||| The type of a constant of Idris's core terms (`constType`), which the
||| flat expressions and their lowering both read.
module Native.Flat.ConstType

import Core.TT.Primitive

%default total

||| The type of a constant.
public export
constType : Constant -> Maybe PrimType
constType (I _) = Just IntType
constType (I8 _) = Just Int8Type
constType (I16 _) = Just Int16Type
constType (I32 _) = Just Int32Type
constType (I64 _) = Just Int64Type
constType (BI _) = Just IntegerType
constType (B8 _) = Just Bits8Type
constType (B16 _) = Just Bits16Type
constType (B32 _) = Just Bits32Type
constType (B64 _) = Just Bits64Type
constType (Str _) = Just StringType
constType (Ch _) = Just CharType
constType (Db _) = Just DoubleType
constType WorldVal = Just WorldType
constType (PrT _) = Nothing
