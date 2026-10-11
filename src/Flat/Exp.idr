||| The *flat regime* is a way of compiling a definition: every value it
||| handles is held in registers, a machine word or a double each, and none
||| needs the heap, so the definition becomes a machine function. Ordinary
||| code, by contrast, holds every value in the one uniform representation a
||| code generator gives all values, boxed on the heap where it does not fit
||| a word. A *flat function* is one compiled in the flat regime.
|||
||| This module is the flat regime's IR, the compiled form of a definition in
||| it: an IR in which every variable carries the layout of its type, and which
||| has no lambda, no lazy value and no boxed object, so a flat form is flat
||| by its shape. `Flat.Translate` translates a definition's typed clauses into
||| it; a code generator that supports the regime lowers it, and the others
||| ignore it.
|||
||| A type appears in it as the flat regime sees it: its layout, the
||| registers its values take, and its skeleton, what a code generator
||| recognises it by. The judgement of a type (`Flat.Judgement`) computes both.
module Flat.Exp

import Core.FC
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

||| One register of a flat value.
public export
data Rep
  = ||| A machine word: an integer of any width up to the word's, a `Char`,
    ||| a constructor's tag, or an address.
    Word
  | ||| An IEEE 754 double.
    Dbl

export
Eq Rep where
  Word == Word = True
  Dbl == Dbl = True
  _ == _ = False

export
Show Rep where
  show Word = "Word"
  show Dbl = "Dbl"

||| The registers a value of a flat type takes, in order. A token, `%World`
||| and anything erased take none; a type with several constructors takes a
||| tag first, then each constructor's fields in turn.
public export
Layout : Type
Layout = List Rep

||| A type as a code generator recognises it: a primitive, or a type or data
||| constructor applied to skeletons, so that `Addr CON` is told from `Addr
||| CLOSURE`. `SOther` stands for anything else, such as an index that is a
||| variable.
public export
data Skeleton
  = SPrim PrimType
  | SCon Name (List Skeleton)
  | SOther

export covering
Show Skeleton where
  show (SPrim t) = show t
  show (SCon n []) = show n
  show (SCon n as) = "(" ++ show n ++ concatMap (\a => " " ++ show a) as ++ ")"
  show SOther = "_"

export
Eq Skeleton where
  SPrim a == SPrim b = a == b
  SCon m as == SCon n bs = m == n && assert_total (as == bs)
  SOther == SOther = True
  _ == _ = False

||| How ordinary code represents the values of a constructor, once
||| `Compiler.Opts.Constructor` has specialised constructors.
public export
data Ordinary
  = ||| As its tag, an integer: a constructor of an enumeration.
    AsTag
  | ||| As one of its run-time fields, by its position among them: the
    ||| constructor of a newtype.
    AsField Nat
  | ||| As an object of this constructor id, holding its run-time fields.
    AsObject Int

export
Show Ordinary where
  show AsTag = "tag"
  show (AsField i) = "field " ++ show i
  show (AsObject i) = "object " ++ show i

mutual
  ||| A flat type as a code generator handles its values: the registers they
  ||| take, and how ordinary code represents them. A type's shape determines
  ||| its layout (`shapeLayout`).
  public export
  data Shape
    = ||| A primitive type.
      PrimShape PrimType
    | ||| A data type, by its constructors in order.
      DataShape (List ConShape)

  ||| A constructor of a flat data type: its tag, how ordinary code represents
  ||| it, and the shapes of its run-time fields.
  public export
  record ConShape where
    constructor MkConShape
    name : Name
    tag : Int
    ordinary : Ordinary
    fields : List Shape

mutual
  ||| The registers a value of the shape takes, as the judgement of its type
  ||| lays them out (`Flat.Judgement`): a primitive's own; a data type of one
  ||| constructor its fields' in turn; one of several a tag, then each
  ||| constructor's fields in turn (`sumSlices`).
  public export
  shapeLayout : Shape -> Layout
  shapeLayout (PrimShape DoubleType) = [Dbl]
  shapeLayout (PrimShape WorldType) = []
  shapeLayout (PrimShape _) = [Word]
  shapeLayout (DataShape []) = []
  shapeLayout (DataShape [c]) = fieldsLayout c.fields
  shapeLayout (DataShape cs@(_ :: _ :: _)) = Word :: consLayout cs

  ||| The registers of a constructor's fields, in turn.
  public export
  fieldsLayout : List Shape -> Layout
  fieldsLayout [] = []
  fieldsLayout (s :: ss) = shapeLayout s ++ fieldsLayout ss

  ||| The registers of each constructor's fields, in turn.
  public export
  consLayout : List ConShape -> Layout
  consLayout [] = []
  consLayout (c :: cs) = fieldsLayout c.fields ++ consLayout cs

||| The shapes of the data types the forms handle, by skeleton.
public export
Shapes : Type
Shapes = List (Skeleton, Shape)

||| A type's shape: a primitive's is its own.
export
shapeOf : Shapes -> Skeleton -> Maybe Shape
shapeOf ss (SPrim t) = Just (PrimShape t)
shapeOf ss sk = lookup sk ss

||| Where the fields of a data type's `i`-th constructor lie among the
||| registers that follow its tag: those before them, theirs, and those
||| after. Every constructor has registers of its own, so the three make up
||| `shapeLayout` after the tag; this is the one place that says so.
export
sumSlices : List ConShape -> Nat -> Maybe (Layout, Layout, Layout)
sumSlices [] _ = Nothing
sumSlices (c :: cs) Z = Just ([], fieldsLayout c.fields, consLayout cs)
sumSlices (c :: cs) (S i)
    = do (before, own, after) <- sumSlices cs i
         pure (fieldsLayout c.fields ++ before, own, after)

mutual
  export covering
  Show Shape where
    show (PrimShape t) = show t
    show (DataShape cs) = "{" ++ concat (intersperse " | " (map showCon cs)) ++ "}"

  covering
  showCon : ConShape -> String
  showCon c = show c.name ++ "#" ++ show c.tag ++ " as " ++ show c.ordinary
              ++ (case c.fields of
                       [] => ""
                       fs => " (" ++ concat (intersperse ", " (map show fs)) ++ ")")

||| A variable of a flat form, with its type's skeleton and layout.
public export
record FlatVar where
  constructor MkFlatVar
  name : Name
  skeleton : Skeleton
  layout : Layout

export covering
Show FlatVar where
  show v = show v.name ++ " : " ++ show v.skeleton ++ " " ++ show v.layout

||| The name of a flat form: the function it is the form of. Forms at static
||| arguments will add those arguments to the name.
public export
FlatName : Type
FlatName = Name

mutual
  ||| A term of the flat regime.
  public export
  data FlatExp : Type where
    ||| A variable.
    FVar : FC -> Name -> FlatExp
    ||| A value bound to a variable, then the scope.
    FLet : FC -> FlatVar -> FlatExp -> FlatExp -> FlatExp
    ||| A constant of a machine type.
    FConst : FC -> Constant -> FlatExp
    ||| A primitive operation.
    FOp : {arity : Nat} -> FC -> PrimFn arity -> Vect arity FlatExp -> FlatExp
    ||| A call of a flat form, with its run-time arguments.
    FCall : FC -> FlatName -> List FlatExp -> FlatExp
    ||| A call of an `%extern` or `%foreign` primitive, with the skeleton
    ||| and layout of its result's type, and its run-time arguments.
    FPrim : FC -> Name -> Skeleton -> Layout -> List FlatExp -> FlatExp
    ||| A constructor, with its tag if its type has several, the skeleton
    ||| and layout of its type, and its run-time fields.
    FCon : FC -> (con : Name) -> (tag : Maybe Int) -> Skeleton -> Layout ->
           List FlatExp -> FlatExp
    ||| A case on a constructor or a constant, with a default.
    FCase : FC -> FlatExp -> List FlatAlt -> Maybe FlatExp -> FlatExp
    ||| The end of the program, with a message.
    FCrash : FC -> String -> FlatExp
    ||| A value whose layout is empty, such as a token or `%World`.
    FNone : FC -> FlatExp

  ||| An alternative of a case.
  public export
  data FlatAlt : Type where
    ||| A constructor, with its tag if its type has several, binding its
    ||| run-time fields.
    FConAlt : (con : Name) -> (tag : Maybe Int) -> List FlatVar -> FlatExp -> FlatAlt
    ||| A constant.
    FConstAlt : Constant -> FlatExp -> FlatAlt

||| A definition's flat form. Its parameters are the run-time arguments of its
||| type, in order, every one of them: the type arity.
public export
record FlatDef where
  constructor MkFlatDef
  name : FlatName
  params : List FlatVar
  resultSkeleton : Skeleton
  result : Layout
  body : FlatExp
  fc : FC

------------------------------------------------------------------------------
-- The type of an expression

||| The layout of a primitive type.
public export
primLayout : PrimType -> Layout
primLayout DoubleType = [Dbl]
primLayout WorldType = []
primLayout _ = [Word]

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

||| The type of a primitive operation's result.
public export
opResult : PrimFn n -> Maybe PrimType
opResult (Add t) = Just t
opResult (Sub t) = Just t
opResult (Mul t) = Just t
opResult (Div t) = Just t
opResult (Mod t) = Just t
opResult (Neg t) = Just t
opResult (ShiftL t) = Just t
opResult (ShiftR t) = Just t
opResult (BAnd t) = Just t
opResult (BOr t) = Just t
opResult (BXOr t) = Just t
opResult (LT _) = Just IntType
opResult (LTE _) = Just IntType
opResult (EQ _) = Just IntType
opResult (GTE _) = Just IntType
opResult (GT _) = Just IntType
opResult (Cast _ t) = Just t
opResult _ = Nothing

||| The skeleton and layout of an expression's value, from its variables'
||| (`var`) and the results of the forms it calls (`form`). Nothing if no
||| value comes of it, a crash or every alternative one, or a form's result
||| is not known.
export
expType : (var : Name -> Maybe (Skeleton, Layout)) -> (form : Name -> Maybe (Skeleton, Layout)) ->
          FlatExp -> Maybe (Skeleton, Layout)
expType var form (FVar _ x) = var x
expType var form (FLet _ fv _ sc) = expType (bound [fv]) form sc
  where
    bound : List FlatVar -> Name -> Maybe (Skeleton, Layout)
    bound vs y = case find (\v => v.name == y) vs of
      Just v => Just (v.skeleton, v.layout)
      Nothing => var y
expType var form (FConst _ k) = (\t => (SPrim t, primLayout t)) <$> constType k
expType var form (FOp _ op _) = (\t => (SPrim t, primLayout t)) <$> opResult op
expType var form (FCall _ n _) = form n
expType var form (FPrim _ _ sk lay _) = Just (sk, lay)
expType var form (FCon _ _ _ sk lay _) = Just (sk, lay)
expType var form (FCase _ _ alts def) = head' (catMaybes (map alt alts ++ [def >>= expType var form]))
  where
    bound : List FlatVar -> Name -> Maybe (Skeleton, Layout)
    bound vs y = case find (\v => v.name == y) vs of
      Just v => Just (v.skeleton, v.layout)
      Nothing => var y
    alt : FlatAlt -> Maybe (Skeleton, Layout)
    alt (FConAlt _ _ vs b) = expType (bound vs) form b
    alt (FConstAlt _ b) = expType var form b
expType var form (FCrash _ _) = Nothing
expType var form (FNone _) = Just (SOther, [])

||| The forms a form calls.
export
formCallees : FlatDef -> List Name
formCallees fd = go fd.body
  where
    go : FlatExp -> List Name
    go (FVar _ _) = []
    go (FLet _ _ val sc) = go val ++ go sc
    go (FConst _ _) = []
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ f as) = f :: concatMap go as
    go (FPrim _ _ _ _ as) = concatMap go as
    go (FCon _ _ _ _ _ as) = concatMap go as
    go (FCase _ sc alts def) = go sc ++ concatMap alt alts ++ maybe [] go def
      where
        alt : FlatAlt -> List Name
        alt (FConAlt _ _ _ b) = go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = []
    go (FNone _) = []

||| The skeletons of the types a form handles: its parameters', its
||| result's, its variables' and its constructors'. The lowering needs the
||| shapes of the data types among them.
export
formSkeletons : FlatDef -> List Skeleton
formSkeletons fd = fd.resultSkeleton :: map skeleton fd.params ++ go fd.body
  where
    go : FlatExp -> List Skeleton
    go (FVar _ _) = []
    go (FLet _ fv val sc) = fv.skeleton :: go val ++ go sc
    go (FConst _ _) = []
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ _ as) = concatMap go as
    go (FPrim _ _ sk _ as) = sk :: concatMap go as
    go (FCon _ _ _ sk _ as) = sk :: concatMap go as
    go (FCase _ sc alts def) = go sc ++ concatMap alt alts ++ maybe [] go def
      where
        alt : FlatAlt -> List Skeleton
        alt (FConAlt _ _ vs b) = map skeleton vs ++ go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = []
    go (FNone _) = []

mutual
  covering
  showExp : Nat -> FlatExp -> String
  showExp i (FVar _ n) = show n
  showExp i (FLet _ v val sc)
      = "let " ++ show v ++ " = " ++ showExp (i + 2) val ++ "\n"
        ++ showIndent i ++ showExp i sc
  showExp i (FConst _ c) = show c
  showExp i (FOp _ op as) = show op ++ showArgs i (toList as)
  showExp i (FCall _ n as) = show n ++ showArgs i as
  showExp i (FPrim _ n _ _ as) = "%prim " ++ show n ++ showArgs i as
  showExp i (FCon _ c t s l as)
      = show c ++ maybe "" (\t => "{" ++ show t ++ "}") t ++ showArgs i as
  showExp i (FCase _ sc alts def)
      = "case " ++ showExp i sc ++ " of"
        ++ concatMap (\a => "\n" ++ showIndent (i + 2) ++ showAlt (i + 4) a) alts
        ++ maybe "" (\d => "\n" ++ showIndent (i + 2) ++ "_ => " ++ showExp (i + 4) d) def
  showExp i (FCrash _ msg) = "crash " ++ show msg
  showExp i (FNone _) = "()"

  covering
  showAlt : Nat -> FlatAlt -> String
  showAlt i (FConAlt c t vs sc)
      = show c ++ maybe "" (\t => "{" ++ show t ++ "}") t
        ++ concatMap (\v => " (" ++ show v ++ ")") vs ++ " => " ++ showExp i sc
  showAlt i (FConstAlt c sc) = show c ++ " => " ++ showExp i sc

  covering
  showArgs : Nat -> List FlatExp -> String
  showArgs i [] = ""
  showArgs i as = "(" ++ concat (intersperse ", " (map (showExp i) as)) ++ ")"

  showIndent : Nat -> String
  showIndent i = pack (replicate i ' ')

export covering
Show FlatExp where
  show = showExp 0

export covering
Show FlatDef where
  show d = show d.name ++ " (" ++ concat (intersperse ", " (map show d.params)) ++ ")"
           ++ " : " ++ show d.resultSkeleton ++ " " ++ show d.result ++ " =\n  "
           ++ showExp 2 d.body
