-- Each carrier of the contract is held as its rep says. The runtime gives
-- every carrier an Idris type (`Carried`); the code generator, which reads
-- carriers as data, lays a value out by judging its Idris type
-- (`Native.Flat.Judgement`). The two must agree, or a value would cross the
-- contract in a register the judgement did not put it in, and be read as
-- something else; Idris cannot check that, since the judgement is the code
-- generator's, so this does. For every carrier, its Idris type is judged to
-- take the one register of the carrier's rep (`Carrier.rep`):
--
--     Carried () (Machine U64)    = Bits64            judged [Word]
--     Carried () (Machine F64)    = Double            judged [Dbl]
--     Carried () (ValueOf Bits64) = Uniform Bits64    judged [Uniform]
--     Carried () Value            = Uniform ()        judged [Uniform]
--     Carried () ByteAddr         = ByteAddr          judged [ByteAddr]
--
-- Every machine code is listed (`listed`), so a new one is judged too.
module Main

import Core.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.TT
import Core.TT.Primitive as Primitive
-- `Core.Context` declares the decoding of definitions, which this defines:
-- a program that makes a context links it
import Core.TTC
import Core.Value
import Data.List
import Data.List.Elem
import Data.String
import Language.Reflection
import Language.Reflection.TT as R
import Language.Reflection.TTImp as R
import Native.Carrier
import Native.Flat.Exp
import Native.Flat.Judgement
import Native.Mach
import Native.Rep
import Native.Runtime.PortTy

%language ElabReflection
%default covering

machs : List Mach
machs = [I8, I16, I32, I64, IWord, U8, U16, U32, U64, Rune, F64]

-- Every machine code is in the list: a new one, missing, fails here.
listed : (m : Mach) -> Elem m Main.machs
listed I8 = %search
listed I16 = %search
listed I32 = %search
listed I64 = %search
listed IWord = %search
listed U8 = %search
listed U16 = %search
listed U32 = %search
listed U64 = %search
listed Rune = %search
listed F64 = %search

carriers : List Carrier
carriers = map Machine machs ++ [ValueOf Bits64, Value, ByteAddr]

-- Each carrier's Idris type, as the elaborator quotes it where this is
-- compiled: `Bits64`, not `Carried () (Machine U64)`.
quoted : List R.TTImp
quoted = %runElab traverse (\c => quote (Carried () c)) carriers

-- The quoted type as the judgement is given a type: a primitive, or a type
-- constructor by its full name, which is all it reads of these.
asNF : R.TTImp -> Maybe ClosedNF
asNF (R.IPrimVal _ (R.PrT t)) = Just (NPrimVal EmptyFC (Primitive.PrT (prim t)))
  where
    prim : R.PrimType -> Primitive.PrimType
    prim R.IntType = Primitive.IntType
    prim R.IntegerType = Primitive.IntegerType
    prim R.Int8Type = Primitive.Int8Type
    prim R.Int16Type = Primitive.Int16Type
    prim R.Int32Type = Primitive.Int32Type
    prim R.Int64Type = Primitive.Int64Type
    prim R.Bits8Type = Primitive.Bits8Type
    prim R.Bits16Type = Primitive.Bits16Type
    prim R.Bits32Type = Primitive.Bits32Type
    prim R.Bits64Type = Primitive.Bits64Type
    prim R.StringType = Primitive.StringType
    prim R.CharType = Primitive.CharType
    prim R.DoubleType = Primitive.DoubleType
    prim R.WorldType = Primitive.WorldType
asNF t = (\n => NTCon EmptyFC n 0 []) <$> head t
  where
    head : R.TTImp -> Maybe Core.Name.Name
    head (R.IVar _ (R.NS (R.MkNS ns) (R.UN (R.Basic n)))) =
      Just
        (Core.Name.NS (mkNamespace (joinBy "." (reverse ns)))
         (Core.Name.UN (Core.Name.Basic n)))
    head (R.IApp _ f _) = head f
    head _ = Nothing

-- The judgement of a type, in a context of nothing: the judgement of a
-- primitive and of these type constructors looks nothing up.
judged : ClosedNF -> IO (Maybe Layout)
judged nf =
  coreRun
    (do defs <- initDefs
        c <- newRef Ctxt defs
        Judgement.layout [] nf)
    (\_ => pure Nothing)
    (\j => pure (case j of
                   Judgement.LaidOut l => Just l
                   _ => Nothing))

main : IO ()
main = do
  results <- traverse check (zip carriers quoted)
  putStrLn (if and (map delay results) then "every carrier agrees" else "a carrier disagrees")
  where
    check : (Carrier, R.TTImp) -> IO Bool
    check (c, t) = do
      l <- maybe (pure Nothing) judged (asNF t)
      let ok = l == Just [Carrier.rep c]
      putStrLn (show t ++ ": " ++ maybe "not laid out" show l
                ++ (if ok then "" else ", but its carrier's rep is " ++ show (Carrier.rep c)))
      pure ok
