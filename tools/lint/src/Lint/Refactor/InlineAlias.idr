||| The refactoring `inline-alias` (`inlineAlias`): a function that only
||| names a term of its parameters (`Op ctx = Opnd (Var ctx)`) replaced, at
||| each use, by that term, and taken out.
|||
||| It is given the function's full name and acts on the file of its module.
||| Each application of it to as many arguments as it has parameters, in
||| any module of the run, becomes its right-hand side with the arguments
||| in the parameters' places: `Op ctx t` is `Opnd (Var ctx) t`. In another
||| module, a name of ours the right-hand side writes is written with its
||| module's path from there, in full (`TermIR.Opnd.Opnd`), and the module
||| imported if it is not; a library's stays as written. It inlines nothing
||| when the function has more than one clause, a parameter is a pattern,
||| a use gives it fewer arguments, or a name the right-hand side writes
||| cannot be told apart.
|||
||| What it leaves for after: the names as the scheme writes them
||| (`qualify-names`), the imports in order (`order-imports`), and the
||| comments that name the function.
module Lint.Refactor.InlineAlias

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.WithData
import Data.List
import Data.List1
import Data.String
import Data.Zippable
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Qualifier
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| What a use of the function becomes: the right-hand side's text, where
||| on its line it starts, the parameters, and the names it writes, each
||| where it is written.
record Alias where
  constructor MkAlias
  text : String
  column : Int
  params : List String
  names : List (FC, Name)
  ||| Whether the term needs no brackets wherever it goes: a name, an
  ||| application, or a term in brackets.
  closed : Bool

||| `inline-alias`: given a function's full name, it inlined.
export
inlineAlias : (arguments : List String) -> Refactoring
inlineAlias args =
  MkRefactoring "inline-alias"
    "replace a function naming a term of its parameters by that term at each use (--arg NAME)"
    True False candidates
  where
    ||| A module's name.
    nameOf : Subject -> String
    nameOf s = show s.file.mod.moduleNS

    ||| The parts of a dotted name.
    partsOf : String -> List String
    partsOf m = forget (split (== '.') m)

    -- the parameters of a clause's left-hand side, if the function is
    -- applied to variables alone
    paramsOf : String -> PTerm -> Maybe (List String)
    paramsOf base (PRef _ (UN (Basic n))) = if n == base then Just [] else Nothing
    paramsOf base (PApp _ f (PRef _ (UN (Basic x)))) = map (++ [x]) (paramsOf base f)
    paramsOf _ _ = Nothing

    closedTerm : PTerm -> Bool
    closedTerm (PRef _ _) = True
    closedTerm (PApp _ _ _) = True
    closedTerm (PBracketed _ _) = True
    closedTerm _ = False

    ||| Where a source location is, for a report.
    place : Subject -> FC -> String
    place t fc = "at line " ++ show (fst (lineSpan fc) + 1) ++ " of " ++ t.file.path

    -- the text a source location spans, if it is on one line
    textAt : Subject -> FC -> Maybe (Int, Int, String)
    textAt s fc = case bounds fc of
      Just ((l, c), (l', c')) => if l == l'
        then Just (l, c, substr (cast c) (cast (c' - c)) (lineOf s l)) else Nothing
      Nothing => Nothing

    -- the function's right-hand side, and the extent of its claim and
    -- clause
    aliasIn : Subject -> String -> Either String (Alias, Extent)
    aliasIn s base = do
      claim <- maybe (Left "it has no claim") Right
                 (find (\d => d.defines == [base] && isClaim d) s.declared)
      def <- maybe (Left "it has no definition") Right
               (find (\d => d.defines == [base] && not (isClaim d)) s.declared)
      (lhs, rhs) <- case def.decl.val of
        PDef [MkPatClause _ lhs rhs []] => Right (lhs, rhs)
        _ => Left "it is not defined by one clause"
      params <- maybe (Left "its parameters are not variables") Right (paramsOf base lhs)
      (l, c, text) <- maybe (Left "its right-hand side is not on one line") Right
        (textAt s (getPTermLoc rhs))
      extent <- extentOf s claim
      let within = \fc => case bounds fc of
                            Just ((l', c'), _) => l' == l && c' >= c && c' < c + cast (length text)
                            Nothing => False
      pure (MkAlias text c params (List.filter (within . fst) s.written) (closedTerm rhs), extent)
      where
        isClaim : Declared -> Bool
        isClaim d = case d.decl.val of
          PClaim _ => True
          _ => False

    -- the module a name the function's module writes comes from, as the
    -- resolution has it: a single one, or none for a library's
    definerOf : Project -> (module', name : String) -> Either String (Maybe String)
    definerOf p m n = case p.resolution of
      Nothing => Left "the modules' uses cannot be resolved: build them first"
      Just r =>
        let definers =
              nub [ u.definer | rm <- r.modules,
                   rm.name == m, u <- rm.uses, u.name == n, not u.searched ] in
        case definers of
          [d] => Right (if any (\t => nameOf t == d) p.files then Just d else Nothing)
          [] => Right Nothing
          _ => Left ("`" ++ n ++ "` has more than one definer")

    -- whether a name written in a file is the function: written bare in
    -- its module, or where the file takes the name from there alone, or
    -- qualified by the module's last parts or its alias
    isAlias : Project -> (module', base : String) -> Subject -> Name -> Bool
    isAlias p m base t (UN (Basic n)) =
      n == base && (nameOf t == m || definerOf p (nameOf t) base == Right (Just m))
    isAlias p m base t (NS ns (UN (Basic n))) =
      n == base && (isSuffixOf (partsOf (show ns)) (partsOf m)
                    || any (\i => show i.path == m && show i.nameAs == show ns) t.file.mod.imports)
    isAlias _ _ _ _ _ = False

    -- a use in a file: the term with the arguments in place, and the
    -- right-hand side's names written from the file
    useEdit : Project -> (module' : String) -> Alias -> Subject -> Applied ->
              Either String (Edit, List String)
    useEdit p m a t u = do
      let k = length a.params
      args <- traverse
        (\fc =>
          maybe (Left ("an argument " ++ place t fc ++ " is on more than one line")) Right
         (textAt t fc))
                       (take k u.args)
      when (length args < k) $
        Left ("it is applied to fewer arguments than it has parameters " ++ place t (fst u.called))
      named <- traverse (nameEdit (map (\(_, _, x) => x) args)) a.names
      body <- maybe (Left "its right-hand side's edits overlap") Right
        (apply (map fst named) a.text)
      let text = if a.closed then body else "(" ++ body ++ ")"
          from = maybe (0, 0) fst (bounds (fst u.called))
          to = case last' args of
                 Just (l, c, x) => (l, c + cast (length x))
                 Nothing => maybe from snd (bounds (fst u.called))
      pure (MkEdit from to text, mapMaybe snd named)
      where
        -- where a name is in the right-hand side's text
        columns : FC -> (Int, Int)
        columns fc = case bounds fc of
          Just ((_, c), (_, c')) => (c - a.column, c' - a.column)
          Nothing => (0, 0)

        -- a name of the right-hand side as the use writes it: an argument
        -- for a parameter; in another module, a name of ours by its path
        -- from there, with the module it needs imported
        nameEdit : List String -> (FC, Name) -> Either String (Edit, Maybe String)
        nameEdit args (fc, n) =
          let at = \x => MkEdit (0, fst (columns fc)) (0, snd (columns fc)) x
          in case n of
               UN (Basic x) =>
                 case lookup x (zip a.params args) of
                   Just arg => Right (at arg, Nothing)
                   Nothing => if nameOf t == m then Right (at x, Nothing) else do
                     d <- definerOf p m x
                     case d of
                       Just d' =>
                         Right (at (joinBy "." (pathFrom (nameOf t) d') ++ "." ++ x), Just d')
                       Nothing => Right (at x, Nothing)
               _ => Right (at (show n), Nothing)

    -- a file's edits: each use replaced, the modules its uses need
    -- imported after its last import
    fileEdits : Project -> (module', base : String) -> Alias -> (exclude : Extent) -> Subject ->
                Either String (List Edit)
    fileEdits p m base a ex t = do
      let ours = \fc => nameOf t /= m
            || (fst (lineSpan fc) < ex.first || fst (lineSpan fc) > ex.last)
          refs = List.filter (\(fc, n) => isAlias p m base t n && ours fc) t.written
          uses =
            longest
              (List.filter (\u => isAlias p m base t (snd u.called) && ours (fst u.called))
               t.applied)
      case List.filter (\(fc, _) => not (any (\u => bounds (fst u.called) == bounds fc) uses))
        refs of
        ((fc, _) :: _) => Left ("it is written unapplied " ++ place t fc)
        [] => pure ()
      edited <- traverse (useEdit p m a t) uses
      let needed =
            nub [ d | (_, ds) <- edited,
                 d <- ds, not (d `elem` map (show . (.path)) t.file.mod.imports), d /= nameOf t ]
          lastImport = foldl (\x, i => max x (fst (lineSpan i.loc))) (-1) t.file.mod.imports
          imports = if null needed then []
            else [insertLines (lastImport + 1) (map ("import " ++) needed)]
      pure (map fst edited ++ imports)
      where
        -- of the applications at one place, the one with every argument
        longest : List Applied -> List Applied
        longest us =
          [ u | u <- us,
            all
              (\v => bounds (fst v.called) /= bounds (fst u.called) || length v.args
               <= length u.args)
           us ]

    -- the function inlined, or why not
    plan : Project -> Subject -> (module', base : String) -> Either String Change
    plan p s m base = do
      (a, ex) <- aliasIn s base
      edits <- traverse (\t => map (t.file.path,) (fileEdits p m base a ex t))
        (List.filter (\t => nameOf t /= m) p.files)
      own <- fileEdits p m base a ex s
      pure
        (MkChange ((s.file.path, cut (linesOf s) ex :: own) :: List.filter (not . null . snd) edits)
         [] [])

    candidates : Project -> Subject -> List Candidate
    candidates p s = case args of
      [full] => case reverse (partsOf full) of
        (base :: rest@(_ :: _)) =>
          let m = joinBy "." (reverse rest) in
          if nameOf s == m && any (\d => base `elem` d.defines) s.declared
            then [candidate ("inline " ++ full) (plan p s m base)] else []
        _ => []
      _ => []
