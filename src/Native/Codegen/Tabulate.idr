||| A table's rows, computed when the program is compiled (`tabulate`): the
||| value of the table at each index of its range, computed by evaluating it,
||| laid out as the words flat code holds it in (`Native.Table` says what a
||| table is).
module Native.Codegen.Tabulate

import Native.Codegen.Bytes
import Native.Codegen.Evaluate
import Native.Codegen.LowerFlat

import Core.CompileExpr
import Core.Core
import Core.Name
import Core.TT.Primitive
import Data.Maybe
import Data.SortedMap

%default covering

||| A table as the program has it: its function, the index of its first row,
||| the words of a row, and its rows, one after another, each word's eight
||| bytes from the lowest.
public export
record Tabulated where
  constructor MkTabulated
  name : Name
  lo : Int
  rowWords : Nat
  bytes : List Bits8

||| The table of the function, over its range: each row the words of its
||| value at an index, in the order of the fields of the value, each a
||| constant, by the evaluation of the function's compiled form among the
||| program's (`Native.Codegen.Evaluate`), each of at most `fuel` steps. Fails if a
||| value is not computed, is not constants, or has a row not as long as
||| the first.
export
tabulate : (compiled : SortedMap Name NamedDef) -> (fuel : Nat) -> Name -> (lo, hi : Int) ->
           Core (Either String Tabulated)
tabulate compiled fuel n lo hi = do
  -- the index alone: its proof of the range is erased, as compiled code has it
  Right vs <- Evaluate.evaluate compiled fuel n [ [Evaluate.VConst (I k)] | k <- [lo .. hi] ]
    | Left err => pure (Left ("the table " ++ show n ++ ": " ++ err))
  pure (rows vs [<] Nothing)
  where
    -- the words of a value: a constant's, or a constructor's fields' in order
    wordsOf : Evaluate.Value -> Maybe (List Integer)
    wordsOf (Evaluate.VConst (Db x)) = Just [Bytes.doubleBits x]
    wordsOf (Evaluate.VConst k) = (\w => [cast w]) <$> LowerFlat.constWord k
    wordsOf (Evaluate.VCon _ _ fs) = concat <$> traverse wordsOf fs
    wordsOf _ = Nothing

    rows : List Evaluate.Value -> SnocList (List Integer) -> Maybe Nat -> Either String Tabulated
    rows [] acc width =
      Right (MkTabulated n lo (fromMaybe 0 width) (concatMap Bytes.le64 (concat (acc <>> []))))
    rows (v :: vs) acc width = case wordsOf v of
      Nothing => Left ("the table " ++ show n ++ " has a value that is not constants")
      Just ws =>
        if maybe False (/= length ws) width
           then Left ("the table " ++ show n ++ " has a row of another length")
           else rows vs (acc :< ws) (Just (length ws))
