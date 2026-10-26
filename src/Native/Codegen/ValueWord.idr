||| What a value the code generator computed as it compiled the program
||| (`Evaluate.Value`) is as a uniform value of ordinary code
||| (`valueWord`), with the static objects that hold it
||| (`StaticObjects`): the one rule the values of the constants a program
||| marks static are laid out by (`Native.Codegen.StaticRead`), as
||| `ConstantWord.constantWord` is for a constant.
|||
||| A value is made bottom up. A number, a string or a double is its
||| constant's word, and the object that holds it, if any, is named after
||| what it holds, as every constant's is; the erased value is its word; a
||| nullary constructor is the static object every use of it shares. A
||| constructor with fields is a `CON` whose fields are its values' words,
||| and an object a maker made (`Types.FromWords`) a `BYTES` of its words.
||| Each of those is made once per distinct content, so that values holding
||| equal values share their objects, as `0 :: primes` holds the cells of
||| `primes`; and is named by how many such objects were made before it, so
||| that the names, and the image, depend only on the order the values are
||| made in. A value held in two places, as the evaluation shares one a
||| `let` binds or an argument passes, is laid out once, found by the
||| number the evaluation gave it (`Evaluate.Value`): the layout walks each
||| constructor and maker's object the evaluation made once, however many
||| paths lead to it, so that it takes as many steps as the evaluation made
||| objects, where a walk of every path could take exponentially many. A
||| type, a function and a delayed value are not laid out as static data,
||| and say why.
module Native.Codegen.ValueWord

import Native.Codegen.ConstantWord
import Native.Codegen.Evaluate

import Core.Name
import Core.Name.Namespace
import Data.SortedMap
import Native.Types.BignumEnc as Types

%default total

||| The static objects values have been made of so far: each by its name,
||| with what it holds, and those named as they were made by what they
||| hold, so that the next value of the same content shares one; and the
||| word of each value laid out, so that the value is not laid out again.
public export
record StaticObjects where
  constructor MkStaticObjects
  ||| Every object, by its name.
  plans : SortedMap Name ConstantWord.StaticPlan
  ||| Each constructor with fields, by its id and its fields' words, each as
  ||| what it is: a fixnum's value, the erased value as none, an object's
  ||| name.
  constructors : SortedMap (Int, List (Either Int64 (Maybe Name))) Name
  ||| Each object a maker made, by its words.
  runs : SortedMap (List Bits64) Name
  ||| The word of each constructor and maker's object laid out so far, by
  ||| the number the evaluation gave it, so that a value held in two
  ||| places is laid out once.
  laid : SortedMap Nat ConstantWord.StaticWord
  ||| How many objects were named as they were made: the next one's number.
  made : Nat

||| No static objects, before any value is made.
export
noObjects : StaticObjects
noObjects = MkStaticObjects empty empty empty empty 0

||| What a value is as a uniform value of ordinary code: its word, and the
||| static objects after it is made, those it is made of among them; or why
||| the value is not laid out as static data. The bignum encoding decides
||| whether a big `Integer` is a value at all (`ConstantWord.constantWord`).
||| Of a value that holds one that is not, the reason says that it holds
||| it, once, however deep it is held.
export
valueWord : Types.BignumEnc -> Evaluate.Value -> StaticObjects ->
            Either String (ConstantWord.StaticWord, StaticObjects)
valueWord bignum = word
  where
    -- the object of this content: the one made before, found by it, or
    -- one made now, named by the count of those made before it, with what
    -- it holds, and found by its content from then on
    shared : Maybe Name -> ConstantWord.StaticPlan -> (Name -> StaticObjects -> StaticObjects) ->
             StaticObjects -> (ConstantWord.StaticWord, StaticObjects)
    shared (Just n) _ _ os = (ConstantWord.Object n, os)
    shared Nothing p found os =
      let n = NS (mkNamespace "_native") (UN (Basic ("static " ++ show os.made))) in
      (ConstantWord.Object n, found n ({ plans $= insert n p, made $= S } os))

    -- a word as what it is, by which a constructor is found by its fields
    content : ConstantWord.StaticWord -> Either Int64 (Maybe Name)
    content (ConstantWord.Fixnum i) = Left i
    content ConstantWord.Erased = Right Nothing
    content (ConstantWord.Object n) = Right (Just n)

    -- the word of the value of this number: the one it was laid out as
    -- before, or the one the layout gives now, kept by the number
    once : Nat -> (StaticObjects -> Either String (ConstantWord.StaticWord, StaticObjects)) ->
           StaticObjects -> Either String (ConstantWord.StaticWord, StaticObjects)
    once k layout os = case lookup k os.laid of
      Just w => Right (w, os)
      Nothing => do
        (w, os') <- layout os
        Right (w, { laid $= insert k w } os')

    -- the objects with the one a word names, if it names one named after
    -- what it holds: a constant's, or every nullary constructor's of an id
    named : Maybe (Name, ConstantWord.StaticPlan) -> StaticObjects -> StaticObjects
    named (Just (n, p)) os = { plans $= insert n p } os
    named Nothing os = os

    -- why a value that ordinary code holds as a closure, a lambda, a
    -- partial application or a delay, is not laid out
    closure : String -> String
    closure what = what ++ ", whose closure the code generator does not lay out as static data yet"

    -- why a value that holds the value that is not laid out is not, said
    -- once: of one held deeper, the holder below said it
    held : Evaluate.Value -> String -> String
    held (Evaluate.VCon _ (Just _) (_ :: _) _) why = why
    held _ why = "a value that holds " ++ why

    mutual
      word : Evaluate.Value -> StaticObjects ->
             Either String (ConstantWord.StaticWord, StaticObjects)
      word (Evaluate.VConst k) os = do
        (w, o) <- ConstantWord.constantWord bignum k
        Right (w, named o os)
      word Evaluate.VErased os = Right (ConstantWord.Erased, os)
      word (Evaluate.VCon _ (Just c) [] _) os =
        Right (ConstantWord.Object (ConstantWord.nullaryCon c),
               named (Just (ConstantWord.nullaryCon c, ConstantWord.Nullary c)) os)
      word (Evaluate.VCon _ (Just c) fs@(_ :: _) i) os = once i (\os0 => do
        (ws, os') <- fields fs os0
        let k = (c, map content ws)
        Right (shared (lookup k os'.constructors) (ConstantWord.Constructor c ws)
                 (\n => { constructors $= insert k n }) os')) os
      word (Evaluate.VCon _ Nothing _ _) os =
        Left "a type, which the code generator does not lay out as static data yet"
      word (Evaluate.VBytes bs i) os = once i (\os0 =>
        let ws = values bs in
        Right
          (shared (lookup ws os0.runs) (ConstantWord.Words ws) (\n => { runs $= insert ws n })
             os0)) os
      word (Evaluate.VLam {}) os = Left (closure "a function")
      -- a function applied to fewer arguments than it takes, which only the
      -- evaluation makes: Idris's compiled form applies each function to
      -- all it takes, a lambda standing for those the source leaves out,
      -- so a constant whose source holds a partial application holds a
      -- lambda. Refused as a lambda is.
      word (Evaluate.VPartial {}) os = Left (closure "a function")
      word (Evaluate.VDelay {}) os = Left (closure "a delayed value")

      -- the words of a constructor's fields, in order
      fields : List Evaluate.Value -> StaticObjects ->
               Either String (List ConstantWord.StaticWord, StaticObjects)
      fields [] os = Right ([], os)
      fields (f :: fs) os = do
        (w, os1) <- mapFst (held f) (word f os)
        (ws, os2) <- fields fs os1
        Right (w :: ws, os2)
