||| A module's concepts (`Concept`): what an importer takes from it, one
||| thing at a time.
|||
||| A concept is a type (a data type, a record, an interface, or a
||| definition whose value is a type) with all that comes with it: its
||| constructors, a record's fields, an interface's methods, its
||| implementations in the module, and the module's functions about it,
||| those whose type mentions it. A function that mentions several of the module's types goes with
||| the type the module is named after, if it is one of them, or else with
||| the first it mentions; an implementation with the first type of the
||| module its parameters name, or else with its interface, if the module
||| defines it. Any other definition is a concept of its own: a constant, a
||| helper about none of the module's types, an implementation of another
||| module's interface for another's type.
module Lint.Concept

import Lint.Finding
import Lint.Refactor.Span
import Lint.Rules
import Lint.Source

import Core.Name
import Core.Name.Namespace
import Core.TT
import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData

%default covering

||| A concept of a module: what it is called (its type's name, or its
||| definition's), the names that are it (as a use names them, an
||| implementation by what it implements, `Show Header`), whether an
||| importer sees it (one of its definitions is exported), the other
||| concepts of the module its definitions refer to, and its size.
public export
record Concept where
  constructor MkConcept
  name : String
  members : List String
  offered : Bool
  refers : List String
  ||| The lines its declarations take, their documentation included.
  size : Nat

||| The lines a piece of a module holds at least to be worth a module of its
||| own: a module costs its preamble, its documentation, imports and
||| `%default`, ten lines or so, and a piece of less than twice that would
||| cost more as a file than it saves its importers. Below it, a piece stays
||| where it is, and a module is too small to stand alone.
export
pieceLines : Nat
pieceLines = 20

||| The concept each of a module's declarations belongs to, by its name.
export
ownerIn : Source.SourceFile -> List Rules.Declared -> Rules.Declared -> String
ownerIn f ds =
  let types = Finding.joined (map typeNames ds)
      interfaces = Finding.joined (map interfaceNames ds)
      placed = belongsTo (keyOf f types) types interfaces
      claimed =
        the (SortedMap String String)
          (fromList [ (n, placed d) | d <- ds, isClaim d, n <- d.defines ])
  in ownerBy placed claimed
  where
    ||| Whether a type is that of a type: one that, past its binders, is `Type`,
    ||| as a synonym's or a type family's is (`Op : Type -> Type -> Type`).
    returnsType : PTerm -> Bool
    returnsType (PPi _ _ _ _ _ r) = returnsType r
    returnsType (NewPi b) = returnsType b.val.scope
    returnsType (Forall b) = returnsType (snd b.val)
    returnsType (PType _) = True
    returnsType _ = False

    typeNames : Rules.Declared -> List String
    typeNames d = case d.decl.val of
      PData {} => d.defines
      PRecord {} => d.defines
      PInterface {} => d.defines
      PClaim c => if returnsType c.type.val.type then d.defines else []
      _ => []

    interfaceNames : Rules.Declared -> List String
    interfaceNames d = case d.decl.val of
      PInterface {} => d.defines
      _ => []

    isClaim : Rules.Declared -> Bool
    isClaim d = case d.decl.val of
      PClaim _ => True
      _ => False

    -- a definition goes with its claim, wherever its body's mentions point
    ownerBy : (Rules.Declared -> String) -> SortedMap String String -> Rules.Declared -> String
    ownerBy placed claimed d = case d.decl.val of
      PDef _ => fromMaybe (placed d) (head' d.defines >>= \n => lookup n claimed)
      _ => placed d

    ||| What each of a module's declarations belongs to, by the concept's name.
    belongsTo : (key : Maybe String) -> (types : List String) -> (interfaces : List String) ->
                Rules.Declared -> String
    belongsTo key types interfaces d = case d.decl.val of
      PData {} => own
      PRecord {} => own
      PInterface {} => own
      PImplementation {} => case d.implementing of
        Just (iface, params) => case find (`elem` types) params of
          Just t => t
          Nothing => if iface `elem` interfaces then iface else unwords (iface :: params)
        Nothing => own
      _ => let mentioned = filter (`elem` types) d.mentions in
           case key of
             Just k => if k `elem` mentioned then k else fromMaybe own (head' mentioned)
             Nothing => fromMaybe own (head' mentioned)
      where
        own : String
        own = fromMaybe "" (head' d.defines)

    ||| The module's key type: the one it is named after, if it defines it.
    keyOf : Source.SourceFile -> List String -> Maybe String
    keyOf f types = find (\t => toLower t == toLower (Rules.lastPart (show f.mod.moduleNS))) types

||| A module's concepts, in the order their first declarations are written.
export
conceptsOf : Source.SourceFile -> List Rules.Declared -> List Concept
conceptsOf f ds =
  let owner = ownerIn f ds
      names = nub (map owner ds)
      memberOf =
        the (SortedMap String String) (fromList [ (m, owner d) | d <- ds, m <- membersOf d ])
  in map (concept owner memberOf) names
  where
    ||| The names a declaration contributes to its concept: those it defines,
    ||| and a type's constructors, fields and methods; an implementation, by
    ||| what it implements.
    membersOf : Rules.Declared -> List String
    membersOf d = case d.decl.val of
      PData _ _ _ (MkPData _ n _ _ cons) => nameRoot n
        :: foldr (\c, rest => map (nameRoot . (.val) . snd) (forget c.val.names) ++ rest) [] cons
      PRecord _ _ _ (MkPRecord n _ _ con fields) =>
        nameRoot n :: maybe [] (\c => [nameRoot c.val]) con
          ++ foldr (\f, rest => map (nameRoot . (.val)) f.names ++ rest) [] fields
      PInterface _ _ n _ _ _ _ body =>
        nameRoot n :: foldr (\m, rest => case m.val of
                                           PClaim c =>
                                             map (nameRoot . (.val) . snd) (forget c.type.val.names)
                                             ++ rest
                                           _ => rest) [] body
      PImplementation {} => maybe [] (\ip => [unwords (fst ip :: snd ip)]) d.implementing
      _ => d.defines

    ||| Whether a declaration makes its concept visible to an importer.
    exportedHere : Rules.Declared -> Bool
    exportedHere d = case d.decl.val of
      PImplementation v _ _ _ _ _ _ _ _ _ => v /= Private
      _ => not (null d.visible)

    linesOf : Rules.Declared -> Nat
    linesOf d = let (a, b) = Refactor.Span.lineSpan d.decl.fc in cast (b - a + 1)

    concept : (Rules.Declared -> String) -> SortedMap String String -> String -> Concept
    concept owner memberOf n =
      let mine = filter (\d => owner d == n) ds
          refs =
            nub
              (filter (/= n)
               (mapMaybe (\m => lookup m memberOf) (Finding.joined (map (.mentions) mine))))
      in MkConcept n (nub (Finding.joined (map membersOf mine))) (any exportedHere mine) refs
        (sum (map linesOf mine))

||| The concept a use of a module's name is of: the one the name is a
||| member of; for an implementation found by search, named by what it
||| implements (`Show Header`), the concept of the first type it names that
||| is one, or else its interface's.
export
conceptOfUse : List Concept -> (name : String) -> (searched : Bool) -> Maybe String
conceptOfUse cs n False = map (.name) (find (\c => n `elem` c.members) cs)
conceptOfUse cs n True = case words n of
  (iface :: heads) => case find (\h => any (\c => c.name == h) cs) heads of
    Just h => Just h
    Nothing => if any (\c => c.name == iface) cs then Just iface else Nothing
  [] => Nothing

||| The concepts a module's concept reaches by its references, through any
||| of the module's concepts, itself not among them unless a cycle leads
||| back to it.
export
reachable : List Concept -> String -> SortedSet String
reachable cs n = go empty (refersOf n)
  where
    refersOf : String -> List String
    refersOf c = maybe [] (.refers) (find (\x => x.name == c) cs)

    go : SortedSet String -> List String -> SortedSet String
    go seen [] = seen
    go seen (c :: rest) = if contains c seen then go seen rest
      else go (insert c seen) (refersOf c ++ rest)
