||| The refactoring `unprime` (`unprime`): a function local to a `where`
||| block whose type has a variable renamed with primes (`h'`, `enc''`),
||| where a scope around it binds the name with fewer, gets the name back,
||| and loses each constraint that then repeats its enclosing declaration's.
|||
||| `scope-helpers` renames a moved function's variables so that it stays as
||| general as it was. Where it is used only at the types of the scope it
||| moved into, the primes and the repeated constraints are a second set of
||| parameters of the same meaning. Whether it is so only the type checker
||| can judge (a traversal under binders is used at a context its user's
||| extends), so the refactoring runs only with a check, and each change it
||| makes is one that checks. A variable callers name in a named argument
||| (`{enc' = enc}`) stays: its callers would change too.
module Lint.Refactor.Unprime

import Lint.Refactor.Change
import Lint.Refactor.Constraints
import Lint.Refactor.Edit
import Lint.Refactor.Free
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.TT
import Core.TT.Binder
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source

%default covering

||| `unprime`: each local function's primed variables given back the names a
||| scope around it binds, its repeated constraints dropped, where that
||| checks.
export
unprime : Refactoring
unprime = MkRefactoring "unprime"
  "give each local function's primed type variables the names a scope around it binds, where that checks; only with a check"
  False True (\_ => candidates)
  where
    -- a name with one prime less, if it has one
    fewer : String -> Maybe String
    fewer v = if isSuffixOf "'" v then Just (substr 0 (length v `minus` 1) v) else Nothing

    -- the nearest name with fewer primes that a scope around binds, and
    -- that the claim does not take as a variable of its own
    target : InnerClaim -> String -> Maybe String
    target ic v = fewer v >>= go
      where
        go : String -> Maybe String
        go t = if contains t ic.variables then Nothing
               else if contains t ic.around then Just t
               else fewer t >>= go

    -- whether the text names the variable in a named argument
    namedSomewhere : String -> String -> Bool
    namedSomewhere text v = isInfixOf ("{" ++ v ++ " =") text || isInfixOf ("{" ++ v ++ "}") text

    -- a word of a constraint renamed
    renameWords : List (String, String) -> String -> String
    renameWords rs w = pack (go (unpack w))
      where
        ident : Char -> Bool
        ident c = isAlphaNum c || c == '_' || c == '\''

        go : List Char -> List Char
        go [] = []
        go cs@(c :: _) =
          if ident c
            then let (word, rest) = span ident cs
                     word' = pack word
                 in unpack (fromMaybe word' (lookup word' rs)) ++ go rest
            else case cs of
              (x :: rest) => x :: go rest
              [] => []

    -- the constraints of a claim's type, each with where it is written
    -- and the end of its `=>` and the spaces after it, on its last line
    spans : List String -> PTerm -> List (((Int, Int), (Int, Int)), String)
    spans ls (PPi _ _ AutoImplicit Nothing a r) =
      (case bounds (getPTermLoc a) of
         Just (st, (el, ec)) =>
           let line = fromMaybe "" (head' (drop (cast el) ls))
               after = unpack (substr (cast ec) (length line) line)
               (sp, more) = span (== ' ') after
           in case more of
                ('=' :: '>' :: rest) =>
                  let sp' = length (fst (span (== ' ') rest)) in
                  [((st, (el, ec + cast (length sp) + 2 + cast sp')), fromMaybe "" (head' (writtenAs ls a)))]
                _ => []
         Nothing => [])
      ++ spans ls r
    spans ls (PPi _ _ _ _ _ r) = spans ls r
    spans _ _ = []

    within : ((Int, Int), (Int, Int)) -> (Int, Int) -> Bool
    within (a, b) p = a <= p && p < b

    -- the constraints of the enclosing declaration, tidy
    enclosing : Subject -> Declared -> List String
    enclosing s d = map tidy (case d.decl.val of
      PImplementation _ _ _ _ cs _ _ _ _ _ => foldr (\c, rest => writtenAs (linesOf s) (snd c) ++ rest) [] cs
      _ => foldr (\c, rest => case c.decl.val of
                                PClaim cd => if any (`elem` d.defines) c.defines then constraintsOf (linesOf s) cd.type.val.type ++ rest else rest
                                _ => rest) [] s.declared)

    -- the change for one local claim, or why it stays
    plan : Subject -> List String -> InnerClaim -> List (String, String) -> Either String Change
    plan s theirs ic rs = do
      let named = filter (namedSomewhere s.text . fst) rs
      when (not (null named)) $ Left ("its callers name `" ++ fst (fromMaybe ("", "") (head' named)) ++ "` in a named argument")
      let sites = sitesOf (allOf (occurrences ic.type :: map clauseAt ic.clauses))
      when (any (\(p, _, _) => p == (-1, -1)) sites) $ Left "a variable occurs where it cannot be renamed"
      let dropped = droppedOf (spans (linesOf s) ic.type)
      pure (inFile s.file.path (renamesOf dropped sites ++ map (\((a, b), _) => MkEdit a b "") dropped))
      where
        -- each place a renamed variable occurs, with its new name
        sitesOf : Occurrences -> List ((Int, Int), String, String)
        sitesOf occ = foldr (\(v, t), rest => map (\p => (p, v, t)) (fromMaybe [] (lookup v occ)) ++ rest) [] rs

        -- the claim's constraints that repeat the enclosing declaration's
        -- once renamed
        droppedOf : List (((Int, Int), (Int, Int)), String) -> List (((Int, Int), (Int, Int)), String)
        droppedOf = filter (\(_, w) => elem (tidy (renameWords rs w)) theirs)

        -- the renames, those within a constraint dropped aside
        renamesOf : List (((Int, Int), (Int, Int)), String) -> List ((Int, Int), String, String) -> List Edit
        renamesOf dropped sites =
          [ MkEdit (l, c) (l, c + cast (length v)) t | ((l, c), v, t) <- sites, not (any (\d => within (fst d) (l, c)) dropped) ]

    -- the local claims of a declaration, with the names around them
    claimsOf : Subject -> SortedSet String -> Declared -> List InnerClaim
    claimsOf s globals d = case d.decl.val of
      PDef cls => claimsWithin globals ofClaim cls
      PImplementation _ _ _ _ cs _ ps _ _ (Just body) =>
        let around = foldr (\t, rest => union (free t) rest) (foldr (\c, rest => union (free (snd c)) rest) empty cs) ps in
        foldr (\m, rest => case m.val of
                             PDef cls => claimsWithin globals around cls ++ rest
                             _ => rest) [] body
      _ => []
      where
        ofClaim : SortedSet String
        ofClaim = foldr (\c, rest => case c.decl.val of
                                       PClaim cd => if any (`elem` d.defines) c.defines then union (typeVariables globals cd.type.val.type) rest else rest
                                       _ => rest) empty s.declared

    candidates : Subject -> List Candidate
    candidates s =
      let globals = fromList (foldr (\d, rest => d.defines ++ rest) [] s.declared) in
      foldr (\d, rest => forDecl globals d ++ rest) [] s.declared
      where
        forDecl : SortedSet String -> Declared -> List Candidate
        forDecl globals d =
          let theirs = enclosing s d in
          mapMaybe (\ic => let rs = mapMaybe (\v => map (v,) (target ic v)) (Prelude.toList ic.variables) in
                           if null rs then Nothing
                           else Just (candidate ("the variables of the claim at line " ++ show (ic.line + 1)) (plan s theirs ic rs)))
                   (claimsOf s globals d)
