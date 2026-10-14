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

import Flat.ConstType

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.TT.Primitive
import Data.Builder
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
  | ||| A value as the ordinary regime holds it (`Flat.Uniform`), opaque to
    ||| flat code.
    Uniform

export
Eq Rep where
  Word == Word = True
  Dbl == Dbl = True
  Uniform == Uniform = True
  _ == _ = False

export
Show Rep where
  show Word = "Word"
  show Dbl = "Dbl"
  show Uniform = "Uniform"

||| The flat regime's type of values held as the ordinary regime holds them.
public export
uniformType : Name
uniformType = NS (mkNamespace "Flat.Uniform") (UN (Basic "Uniform"))

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
  -- lint: allow trust-escape: the arguments are parts of the skeletons, which list equality hides
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
    | ||| `Uniform a`: the value as ordinary code holds it, unchanged.
      UniformShape

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
  export covering
  Show Shape where
    show (PrimShape t) = show t
    show (DataShape cs) = "{" ++ concat (intersperse " | " (map showCon cs)) ++ "}"
      where
        covering
        showCon : ConShape -> String
        showCon c = show c.name ++ "#" ++ show c.tag ++ " as " ++ show c.ordinary
                    ++ (case c.fields of
                             [] => ""
                             fs => " (" ++ concat (intersperse ", " (map show fs)) ++ ")")
    show UniformShape = "uniform"

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
  shapeLayout UniformShape = [Uniform]

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
  data Exp : Type where
    ||| A variable.
    FVar : FC -> Name -> Exp
    ||| A value bound to a variable, then the scope.
    FLet : FC -> FlatVar -> Exp -> Exp -> Exp
    ||| A constant of a machine type.
    FConst : FC -> Constant -> Exp
    ||| A primitive operation.
    FOp : {arity : Nat} -> FC -> PrimFn arity -> Vect arity Exp -> Exp
    ||| A call of a flat form, with its run-time arguments.
    FCall : FC -> FlatName -> List Exp -> Exp
    ||| A call of an `%extern` or `%foreign` primitive, with the skeleton
    ||| and layout of its result's type, and its run-time arguments.
    FPrim : FC -> Name -> Skeleton -> Layout -> List Exp -> Exp
    ||| A constructor, with its tag if its type has several, the skeleton
    ||| and layout of its type, and its run-time fields.
    FCon : FC -> (con : Name) -> (tag : Maybe Int) -> Skeleton -> Layout ->
           List Exp -> Exp
    ||| A case on a constructor or a constant, with a default.
    FCase : FC -> Exp -> List FlatAlt -> Maybe Exp -> Exp
    ||| The end of the program, with a message.
    FCrash : FC -> String -> Exp
    ||| A value whose layout is empty, such as a token or `%World`.
    FNone : FC -> Exp

  ||| An alternative of a case.
  public export
  data FlatAlt : Type where
    ||| A constructor, with its tag if its type has several, binding its
    ||| run-time fields.
    FConAlt : (con : Name) -> (tag : Maybe Int) -> List FlatVar -> Exp -> FlatAlt
    ||| A constant.
    FConstAlt : Constant -> Exp -> FlatAlt

||| An expression as text in pieces, each line after the first indented by
||| `i`: appending strings level by level would copy the text below at
||| each level.
covering
expPieces : Nat -> Exp -> Builder String
expPieces i exp = case exp of
  FVar _ n => single (show n)
  FLet _ v val sc
     => single ("let " ++ show v ++ " = ") <+> expPieces (i + 2) val <+> single "\n"
        <+> single (showIndent i) <+> expPieces i sc
  FConst _ c => single (show c)
  FOp _ op as => single (show op) <+> argPieces i (toList as)
  FCall _ n as => single (show n) <+> argPieces i as
  FPrim _ n _ _ as => single ("%prim " ++ show n) <+> argPieces i as
  FCon _ c t s l as
     => single (show c ++ maybe "" (\t => "{" ++ show t ++ "}") t) <+> argPieces i as
  FCase _ sc alts def
     => single "case " <+> expPieces i sc <+> single " of"
        <+> concatMap (\a => single ("\n" ++ showIndent (i + 2)) <+> altPieces (i + 4) a) alts
        <+> maybe neutral (\d => single ("\n" ++ showIndent (i + 2) ++ "_ => ") <+> expPieces (i + 4) d) def
  FCrash _ msg => single ("crash " ++ show msg)
  FNone _ => single "()"
  where
    covering
    altPieces : Nat -> FlatAlt -> Builder String
    altPieces i (FConAlt c t vs sc)
        = single (show c ++ maybe "" (\t => "{" ++ show t ++ "}") t
                  ++ fastConcat (map (\v => " (" ++ show v ++ ")") vs) ++ " => ")
          <+> expPieces i sc
    altPieces i (FConstAlt c sc) = single (show c ++ " => ") <+> expPieces i sc

    covering
    argPieces : Nat -> List Exp -> Builder String
    argPieces i [] = neutral
    argPieces i as = single "(" <+> concat (intersperse (single ", ") (map (expPieces i) as)) <+> single ")"

    showIndent : Nat -> String
    showIndent i = pack (replicate i ' ')

export covering
Show Exp where
  show e = fastConcat (toList (expPieces 0 e))

||| A definition's flat form. Its parameters are the run-time arguments of its
||| type, in order, every one of them: the type arity.
public export
record FlatDef where
  constructor MkFlatDef
  name : FlatName
  params : List FlatVar
  resultSkeleton : Skeleton
  result : Layout
  body : Exp
  fc : FC

||| A definition's flat form as text in pieces: what `show` joins, and what
||| a dump writes a piece at a time.
export covering
defPieces : FlatDef -> Builder String
defPieces d =
  single (show d.name ++ " (" ++ concat (intersperse ", " (map show d.params)) ++ ")"
          ++ " : " ++ show d.resultSkeleton ++ " " ++ show d.result ++ " =\n  ")
  <+> expPieces 2 d.body

export covering
Show FlatDef where
  show d = fastConcat (toList (defPieces d))

------------------------------------------------------------------------------
-- The type of an expression

||| The layout of a primitive type.
export
primLayout : PrimType -> Layout
primLayout DoubleType = [Dbl]
primLayout WorldType = []
primLayout _ = [Word]

||| The skeleton and layout of an expression's value, from its variables'
||| (`var`) and the results of the forms it calls (`form`). Nothing if no
||| value comes of it, a crash or every alternative one, or a form's result
||| is not known.
export
expType : (var : Name -> Maybe (Skeleton, Layout)) -> (form : Name -> Maybe (Skeleton, Layout)) ->
          Exp -> Maybe (Skeleton, Layout)
expType var form (FVar _ x) = var x
expType var form (FLet _ fv _ sc) = expType (bound [fv]) form sc
  where
    bound : List FlatVar -> Name -> Maybe (Skeleton, Layout)
    bound vs y = case find (\v => v.name == y) vs of
      Just v => Just (v.skeleton, v.layout)
      Nothing => var y
expType var form (FConst _ k) = (\t => (SPrim t, primLayout t)) <$> constType k
expType var form (FOp _ op _) = (\t => (SPrim t, primLayout t)) <$> opResult op
  where
    -- The type of a primitive operation's result.
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
formCallees fd = toList (go fd.body)
  where
    go : Exp -> Builder Name
    go (FVar _ _) = neutral
    go (FLet _ _ val sc) = go val <+> go sc
    go (FConst _ _) = neutral
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ f as) = single f <+> concatMap go as
    go (FPrim _ _ _ _ as) = concatMap go as
    go (FCon _ _ _ _ _ as) = concatMap go as
    go (FCase _ sc alts def) = go sc <+> concatMap alt alts <+> maybe neutral go def
      where
        alt : FlatAlt -> Builder Name
        alt (FConAlt _ _ _ b) = go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = neutral
    go (FNone _) = neutral

||| The primitives a form calls.
export
formPrims : FlatDef -> List Name
formPrims fd = toList (go fd.body)
  where
    go : Exp -> Builder Name
    go (FVar _ _) = neutral
    go (FLet _ _ val sc) = go val <+> go sc
    go (FConst _ _) = neutral
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ _ as) = concatMap go as
    go (FPrim _ p _ _ as) = single p <+> concatMap go as
    go (FCon _ _ _ _ _ as) = concatMap go as
    go (FCase _ sc alts def) = go sc <+> concatMap alt alts <+> maybe neutral go def
      where
        alt : FlatAlt -> Builder Name
        alt (FConAlt _ _ _ b) = go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = neutral
    go (FNone _) = neutral

||| The skeletons of the types a form handles: its parameters', its
||| result's, its variables' and its constructors'. The lowering needs the
||| shapes of the data types among them.
export
formSkeletons : FlatDef -> List Skeleton
formSkeletons fd = toList (single fd.resultSkeleton <+> piece (map skeleton fd.params) <+> go fd.body)
  where
    go : Exp -> Builder Skeleton
    go (FVar _ _) = neutral
    go (FLet _ fv val sc) = single fv.skeleton <+> go val <+> go sc
    go (FConst _ _) = neutral
    go (FOp _ _ as) = concatMap go (toList as)
    go (FCall _ _ as) = concatMap go as
    go (FPrim _ _ sk _ as) = single sk <+> concatMap go as
    go (FCon _ _ _ sk _ as) = single sk <+> concatMap go as
    go (FCase _ sc alts def) = go sc <+> concatMap alt alts <+> maybe neutral go def
      where
        alt : FlatAlt -> Builder Skeleton
        alt (FConAlt _ _ vs b) = piece (map skeleton vs) <+> go b
        alt (FConstAlt _ b) = go b
    go (FCrash _ _) = neutral
    go (FNone _) = neutral
