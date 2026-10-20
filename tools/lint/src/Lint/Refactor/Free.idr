||| What a piece of code leaves to its surroundings (`free`): the names it
||| refers to that it does not bind itself, written without a namespace,
||| each with where it occurs (`occurrences`).
|||
||| Those are the names a variable bound around the code would capture, so a
||| refactoring that moves code into another scope checks them against what
||| that scope binds, and renames what it must where it occurs. Each binding
||| form is followed: lambdas, `let`s, `case` alternatives, local
||| definitions, `do` and comprehension binds, and the binders of types. A
||| name only a type mentions, unbound there, is free: at the top it would
||| be bound implicitly, and under a binder of the same name it would not.
module Lint.Refactor.Free

import Core.FC
import Core.Name
import Core.TT
import Core.TT.Binder
import Core.WithData
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules

%default covering

||| Free names, each with the positions it occurs at (line and column from
||| 0); a position of `(-1, -1)` is an occurrence with no place to rename.
public export
Occurrences : Type
Occurrences = SortedMap String (List (Int, Int))

||| What a declaration of a form the analysis does not follow is taken to
||| leave free: a name no code has, which no scope binds, so that whoever
||| asks knows it does not know.
export
unknown : String
unknown = "?"

||| Whether a name is written as a variable is: starting with a lower-case
||| letter or an underscore. Only such a name can be bound by a pattern or
||| a binder, so only such a name can be captured.
export
isVariable : String -> Bool
isVariable n = case unpack n of
  (c :: _) => isLower c || c == '_'
  [] => False

||| The names local declarations define, those of `mutual` blocks included.
export
definedBy : List PDecl -> List String
definedBy = foldr (\d, rest => here d ++ rest) []
  where
    here : PDecl -> List String
    here d = case d.val of
      PMutual ds => definedBy ds
      _ => Rules.definesOf d

||| A name as a variable could be written, plain and unqualified, occurring
||| at the start of a source location.
named : FC -> Name -> Occurrences
named fc (UN (Basic s)) = singleton s [start fc]
  where
    start : FC -> (Int, Int)
    start (MkFC _ p _) = p
    start (MkVirtualFC _ p _) = p
    start EmptyFC = (-1, -1)
named _ _ = empty

||| A binder's name, as a set.
plainSet : Name -> SortedSet String
plainSet (UN (Basic s)) = singleton s
plainSet _ = empty

both : Occurrences -> Occurrences -> Occurrences
both = mergeWith (++)

||| Occurrences put together.
export
allOf : List Occurrences -> Occurrences
allOf = foldr both empty

||| The occurrences, those of the names aside.
except : Occurrences -> SortedSet String -> Occurrences
except o ns = foldr delete o (Prelude.toList ns)

||| The names of occurrences, as a set.
export
namesOf : Occurrences -> SortedSet String
namesOf o = fromList (keys o)

mutual
  ||| The names a pattern binds: those it mentions that are written as
  ||| variables are.
  export
  boundBy : PTerm -> SortedSet String
  boundBy p = fromList (filter isVariable (keys (occurrences p)))

  ||| The names a term refers to and does not bind, with where each occurs.
  export
  occurrences : PTerm -> Occurrences
  occurrences term = case term of
    PRef fc n => named fc n
    NewPi b =>
      both (inBinder b.val.binder) (except (occurrences b.val.scope) (binderNames b.val.binder))
    Forall b =>
      except (occurrences (snd b.val))
        (foldr (\n, rest => union (plainSet n.val) rest) empty (forget (fst b.val)))
    PPi _ _ info n a r =>
      allOf [inInfo info, occurrences a, except (occurrences r) (maybe empty plainSet n)]
    PLam _ _ info pat a sc =>
      allOf [inInfo info, occurrences a, except (occurrences sc) (boundBy pat)]
    PLet _ _ pat ty val sc alts =>
      allOf [occurrences ty,
             occurrences val, except (occurrences sc) (boundBy pat), allOf (map clauseAt alts)]
    PCase _ _ scr alts => both (occurrences scr) (allOf (map clauseAt alts))
    PLocal _ ds sc =>
      except (both (allOf (map declAt ds)) (occurrences sc)) (fromList (definedBy ds))
    PUpdate _ us => allOf (map inUpdate us)
    PApp _ f x => both (occurrences f) (occurrences x)
    PWithApp _ f x => both (occurrences f) (occurrences x)
    PNamedApp _ f _ x => both (occurrences f) (occurrences x)
    PAutoApp _ f x => both (occurrences f) (occurrences x)
    PDelayed _ _ t => occurrences t
    PDelay _ t => occurrences t
    PForce _ t => occurrences t
    PSearch _ _ => empty
    PPrimVal _ _ => empty
    PQuote _ t => occurrences t
    PQuoteName _ _ => empty
    PQuoteDecl _ ds => allOf (map declAt ds)
    PUnquote _ t => occurrences t
    PRunElab _ t => occurrences t
    PHole _ _ _ => empty
    PType _ => empty
    PAs fc _ n t => both (named fc n) (occurrences t)
    PDotted _ t => occurrences t
    PImplicit _ => empty
    PInfer _ => empty
    POp _ l op r => allOf [inLeft l.val, inOp op.val, occurrences r]
    PPrefixOp _ op t => both (inOp op.val) (occurrences t)
    PSectionL _ op t => both (inOp op.val) (occurrences t)
    PSectionR _ t op => both (occurrences t) (inOp op.val)
    PEq _ a b => both (occurrences a) (occurrences b)
    PBracketed _ t => occurrences t
    PString _ _ ss => allOf (map inStr ss)
    PMultiline _ _ _ sss => allOf (map (allOf . map inStr) sss)
    PDoBlock _ _ ss => inDo ss
    PBang _ t => occurrences t
    PIdiom _ _ t => occurrences t
    PList _ _ xs => allOf (map (occurrences . snd) xs)
    PSnocList _ _ xs => allOf (map (occurrences . snd) (xs <>> []))
    PPair _ a b => both (occurrences a) (occurrences b)
    PDPair _ _ a b c => allOf [occurrences a, occurrences b, occurrences c]
    PUnit _ => empty
    PIfThenElse _ a b c => allOf [occurrences a, occurrences b, occurrences c]
    PComprehension fc t ss => inDo (ss ++ [DoExp fc t])
    PRewrite _ a b => both (occurrences a) (occurrences b)
    PRange _ a b c => allOf [occurrences a, maybe empty occurrences b, occurrences c]
    PRangeStream _ a b => both (occurrences a) (maybe empty occurrences b)
    PPostfixApp _ t _ => occurrences t
    PPostfixAppPartial _ _ => empty
    PUnifyLog _ _ t => occurrences t
    PWithUnambigNames _ _ t => occurrences t
    where
      inUpdate : PFieldUpdate -> Occurrences
      inUpdate (PSetField _ t) = occurrences t
      inUpdate (PSetFieldApp _ t) = occurrences t

      inLeft : OperatorLHSInfo PTerm -> Occurrences
      inLeft (NoBinder l) = occurrences l
      inLeft (BindType n ty) = both (occurrences n) (occurrences ty)
      inLeft (BindExpr n e) = both (occurrences n) (occurrences e)
      inLeft (BindExplicitType n ty e) = allOf [occurrences n, occurrences ty, occurrences e]

      inDo : List PDo -> Occurrences
      inDo [] = empty
      inDo (DoExp _ t :: rest) = both (occurrences t) (inDo rest)
      inDo (DoBind _ _ n _ ty t :: rest) =
        allOf [maybe empty occurrences ty, occurrences t, except (inDo rest) (plainSet n)]
      inDo (DoBindPat _ pat ty t alts :: rest) =
        allOf [maybe empty occurrences ty,
               occurrences t, allOf (map clauseAt alts), except (inDo rest) (boundBy pat)]
      inDo (DoLet _ _ n _ ty t :: rest) =
        allOf [occurrences ty, occurrences t, except (inDo rest) (plainSet n)]
      inDo (DoLetPat _ pat ty t alts :: rest) =
        allOf [occurrences ty,
               occurrences t, allOf (map clauseAt alts), except (inDo rest) (boundBy pat)]
      inDo (DoLetLocal _ ds :: rest) =
        except (both (allOf (map declAt ds)) (inDo rest)) (fromList (definedBy ds))
      inDo (DoRewrite _ t :: rest) = both (occurrences t) (inDo rest)

      -- an operator's name, at no place a rename could reach
      inOp : OpStr -> Occurrences
      inOp (OpSymbols n) = map (const [(-1, -1)]) (named EmptyFC n)
      inOp (Backticked n) = map (const [(-1, -1)]) (named EmptyFC n)

      inStr : PStr -> Occurrences
      inStr (StrLiteral _ _) = empty
      inStr (StrInterp _ t) = occurrences t

  ||| The names a clause refers to and does not bind, with where each
  ||| occurs: its left-hand side's variables and its `where` block's
  ||| definitions are bound in it.
  export
  clauseAt : PClause -> Occurrences
  clauseAt (MkPatClause _ lhs rhs wh) =
    except (both (occurrences rhs) (allOf (map declAt wh)))
      (union (boundBy lhs) (fromList (definedBy wh)))
  clauseAt (MkWithClause _ lhs problems _ cls) =
    except
      (both (allOf (map (occurrences . (.withRigValue)) (forget problems)))
       (allOf (map clauseAt cls)))
        (boundBy lhs)
  clauseAt (MkImpossible _ _) = empty

  ||| The names a declaration refers to and does not bind, with where each
  ||| occurs: a claim's type, a definition's clauses, a `mutual` block's
  ||| declarations with their own names bound; any other declaration leaves
  ||| `unknown`, at no place.
  export
  declAt : PDecl -> Occurrences
  declAt d = case d.val of
    PClaim c => occurrences c.type.val.type
    PDef cls => allOf (map clauseAt cls)
    PMutual ds => except (allOf (map declAt ds)) (fromList (definedBy ds))
    _ => singleton unknown [(-1, -1)]

  inInfo : PiInfo PTerm -> Occurrences
  inInfo (DefImplicit t) = occurrences t
  inInfo _ = empty

  inBinder : PBinder -> Occurrences
  inBinder b = both (inInfo b.info) (occurrences b.bind.type)

  binderNames : PBinder -> SortedSet String
  binderNames b = foldr (\n, rest => union (plainSet n.val) rest) empty (forget b.bind.names)

||| The names a term refers to and does not bind.
export
free : PTerm -> SortedSet String
free = namesOf . occurrences

||| The names a clause refers to and does not bind.
export
inClause : PClause -> SortedSet String
inClause = namesOf . clauseAt

||| The names a declaration refers to and does not bind: `unknown` among
||| them if the analysis does not follow it.
export
inDecl : PDecl -> SortedSet String
inDecl = namesOf . declAt

||| The names a type binds or leaves free. In the clauses of the function it
||| is the type of, those it binds are bound, as its implicits are.
export
typeNames : PTerm -> SortedSet String
typeNames (PPi _ _ info n a r) =
  union (maybe empty plainSet n) (union (namesOf (inInfo info)) (union (free a) (typeNames r)))
typeNames (NewPi b) =
  union (binderNames b.val.binder) (union (namesOf (inBinder b.val.binder)) (typeNames b.val.scope))
typeNames (Forall b) =
  union (foldr (\n, rest => union (plainSet n.val) rest) empty (forget (fst b.val)))
    (typeNames (snd b.val))
typeNames t = free t

||| The names a type binds implicitly by a binder of its own, `{x : T}`, an
||| auto-implicit or a default one: those its clauses have in scope.
export
implicitBinders : PTerm -> SortedSet String
implicitBinders (PPi _ _ info n _ r) =
  union (if isImplicit info then maybe empty plainSet n else empty) (implicitBinders r)
  where
    isImplicit : PiInfo PTerm -> Bool
    isImplicit Explicit = False
    isImplicit _ = True
implicitBinders (NewPi b) =
  union (case b.val.binder.info of
           Explicit => empty
           _ => binderNames b.val.binder)
        (implicitBinders b.val.scope)
implicitBinders (Forall b) =
  union (foldr (\n, rest => union (plainSet n.val) rest) empty (forget (fst b.val)))
    (implicitBinders (snd b.val))
implicitBinders _ = empty

||| Where a type binds a name by a binder of its own that is not explicit,
||| `{n : T}`, and where it refers to it under that binder: the places a
||| rename of the binder changes. A binder written with no place to rename
||| gives `(-1, -1)`.
export
implicitSites : String -> PTerm -> List (Int, Int)
implicitSites n (NewPi b) =
  case b.val.binder.info of
    Explicit => implicitSites n b.val.scope
    _ => case filter (\x => x.val == UN (Basic n)) (forget b.val.binder.bind.names) of
           [] => implicitSites n b.val.scope
           xs => foldr (\x, rest => fromMaybe [] (lookup n (named x.fc x.val)) ++ rest) [] xs
                 ++ fromMaybe [] (lookup n (occurrences b.val.scope))
implicitSites n (PPi _ _ info (Just x) _ r) = case info of
  Explicit => implicitSites n r
  _ => if x == UN (Basic n) then [(-1, -1)] else implicitSites n r
implicitSites n (PPi _ _ _ Nothing _ r) = implicitSites n r
implicitSites n (Forall b) = implicitSites n (snd b.val)
implicitSites _ _ = []

||| The names a term applies as functions, at the head of an application:
||| globals, never variables a type binds implicitly.
export
heads : PTerm -> SortedSet String
heads (PApp _ f x) = union (headOf f) (union (heads f) (heads x))
  where
    headOf : PTerm -> SortedSet String
    headOf (PRef _ n) = plainSet n
    headOf (PApp _ g _) = headOf g
    headOf (PNamedApp _ g _ _) = headOf g
    headOf (PAutoApp _ g _) = headOf g
    headOf (PBracketed _ g) = headOf g
    headOf _ = empty
heads (PNamedApp _ f _ x) = union (heads f) (heads x)
heads (PAutoApp _ f x) = union (heads f) (heads x)
heads (PPi _ _ _ _ a r) = union (heads a) (heads r)
heads (NewPi b) = union (heads b.val.binder.bind.type) (heads b.val.scope)
heads (Forall b) = heads (snd b.val)
heads (PBracketed _ t) = heads t
heads (PPair _ a b) = union (heads a) (heads b)
heads (PDPair _ _ a b c) = union (heads a) (union (heads b) (heads c))
heads (PEq _ a b) = union (heads a) (heads b)
heads (POp _ l _ r) = union (heads r) (case l.val of NoBinder x => heads x; _ => empty)
heads (PDelayed _ _ t) = heads t
heads (PPostfixApp _ t _) = heads t
heads _ = empty

||| The variables of a type: the names it binds, and those it leaves free
||| that a type binds implicitly, written as variables are and never at the
||| head of an application, nor among the module's own `globals`.
export
typeVariables : (globals : SortedSet String) -> PTerm -> SortedSet String
typeVariables globals t =
  let hs = heads t
      bound = difference (typeNames t) (free t)
  in union bound
    (fromList
      (filter (\n => isVariable n && not (contains n hs) && not (contains n globals))
       (Prelude.toList (free t))))

||| A claim within clauses: the line its declaration starts at, the
||| variables its type leaves free, the names the scopes around it bind, its
||| type, and the clauses of the function it declares.
public export
record InnerClaim where
  constructor MkInnerClaim
  line : Int
  variables : SortedSet String
  around : SortedSet String
  type : PTerm
  clauses : List PClause

||| The claims within clauses, in their `where` blocks at any depth, starting
||| from the names `around` them; the variables of each are those of
||| `typeVariables`, the module's `globals` aside. A variable a claim's type
||| leaves free that the scopes around it bind means theirs; any other is
||| bound implicitly, afresh.
export
claimsWithin : (globals, around : SortedSet String) -> List PClause -> List InnerClaim
claimsWithin globals around cls = foldr (\cl, rest => inPat cl ++ rest) [] cls
  where
    line : PDecl -> Int
    line d = case d.fc of
      MkFC _ (l, _) _ => l
      MkVirtualFC _ (l, _) _ => l
      EmptyFC => -1

    -- a local function's type's names, from its claim among the block's
    typeOf : List PDecl -> List String -> SortedSet String
    typeOf ds names = foldr (\d, rest => case d.val of
                                         PClaim c => if any (`elem` names) (Rules.definesOf d)
                                           then union (typeNames c.type.val.type) rest else rest
                                         _ => rest) empty ds

    -- the clauses of the local function a claim among the block's declares
    defsOf : List PDecl -> List String -> List PClause
    defsOf ds names = foldr (\d, rest => case d.val of
                                         PDef cs => if any (`elem` names) (Rules.definesOf d)
                                           then cs
                                           ++ rest else rest
                                         _ => rest) [] ds

    block : SortedSet String -> List PDecl -> List PDecl -> List InnerClaim
    block env siblings = foldr (\d, rest => one d ++ rest) []
      where
        one : PDecl -> List InnerClaim
        one d = case d.val of
          PClaim c =>
            [MkInnerClaim (line d)
              (intersection (free c.type.val.type) (typeVariables globals c.type.val.type)) env
                          c.type.val.type (defsOf siblings (Rules.definesOf d))]
          PDef cs => claimsWithin globals (union env (typeOf siblings (Rules.definesOf d))) cs
          PMutual ms => block env siblings ms
          _ => []

    inPat : PClause -> List InnerClaim
    inPat (MkPatClause _ lhs _ wh) = let env =
                                           union around
                                             (union (boundBy lhs) (fromList (definedBy wh))) in
                                               block env wh wh
    inPat (MkWithClause _ lhs _ _ cs) = claimsWithin globals (union around (boundBy lhs)) cs
    inPat (MkImpossible _ _) = []
