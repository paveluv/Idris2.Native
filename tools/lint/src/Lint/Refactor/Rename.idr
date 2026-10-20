||| The refactoring `rename` (`rename`): a name a module defines (a type, a
||| constructor, a function) given another, where it is defined and at every
||| use, in every file of the run.
|||
||| It is given the name with its module's path, `Native.Runtime.Space.grow`,
||| and the new name, `extend`. In the module, every occurrence of the name in
||| its code is renamed, comments and string literals aside: there it can
||| mean only the module's own. In another file, a use is renamed where the
||| resolution of the modules from their TTCs (`Lint.Resolution`) says the
||| file takes the name from the module, and the use is written bare or
||| qualified by the module's alias or by last parts of its path
||| (`Runtime.Space.grow`, `Space.grow`): the root changes, the qualifier
||| stays. It
||| renames nothing when the module, or a file that uses the name, defines
||| the new name already; when the module has the new name and not the old,
||| a rename made before, it renames the uses left, such as a program's
||| that was not among the files.
|||
||| What it leaves for after: the comments that name the old name, which
||| only a person can tell from prose, and the module's own name, which
||| `rename-module` changes.
module Lint.Refactor.Rename

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List1
import Data.String
import Data.Zippable
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Finding
import Lint.Resolution
import Lint.Rules
import Lint.Source

%default covering

||| `rename`: given a name with its module's path and a new name, the name
||| renamed where it is defined and wherever it is used.
export
rename : (arguments : List String) -> Refactoring
rename args =
  MkRefactoring "rename"
    "rename a name a module defines (--arg MODULE.NAME --arg NEW), at its definition and every use"
    True False candidates
  where
    ||| The names a declaration defines: its own, those it exports, and a
    ||| record's constructor, which neither lists.
    definedBy : Rules.Declared -> List String
    definedBy d = d.defines ++ d.visible ++ case d.decl.val of
      PRecord _ _ _ (MkPRecord _ _ _ (Just c) _) => [nameRoot c.val]
      _ => []

    ||| The module and the name of a name with its module's path.
    split' : String -> Maybe (String, String)
    split' q = case reverse (forget (split (== '.') q)) of
      (n :: m@(_ :: _)) => Just (joinBy "." (reverse m), n)
      _ => Nothing

    ident : Char -> Bool
    ident c = isAlphaNum c || c == '_' || c == '\''

    ||| A line's code: what precedes a comment, `--` or `|||`, with string
    ||| literals blanked, so that a name inside one is not taken for a use.
    code : String -> String
    code l = pack (go False (unpack l))
      where
        go : (inString : Bool) -> List Char -> List Char
        go _ [] = []
        go False ('-' :: '-' :: _) = []
        go False ('|' :: '|' :: '|' :: _) = []
        go False ('"' :: cs) = '"' :: go True cs
        go True ('\\' :: _ :: cs) = ' ' :: ' ' :: go True cs
        go True ('"' :: cs) = '"' :: go False cs
        go True (_ :: cs) = ' ' :: go True cs
        go False (c :: cs) = c :: go False cs

    ||| The columns of a line's code where the word starts as a whole word.
    wordsAt : String -> String -> List Int
    wordsAt w l = go 0 (unpack (code l))
      where
        ws : List Char
        ws = unpack w

        go : Int -> List Char -> List Int
        go _ [] = []
        go i cs@(c :: more) =
          if isPrefixOf ws cs && not (maybe False ident (head' (drop (length ws) cs)))
             then i :: go (i + cast (length ws)) (drop (length ws) cs)
             else if ident c then let (word, rest) =
                                        span ident cs in go (i + cast (length word)) rest
             else go (i + 1) more

    ||| In the defining module, every whole-word occurrence of the name in
    ||| its code.
    ownEdits : (old, new : String) -> Subject -> List Edit
    ownEdits old new s =
      [ MkEdit (l, c) (l, c + cast (length old)) new
        | (l, line) <- zip [0 .. cast (length (Subject.linesOf s))] (Subject.linesOf s), c <- wordsAt old line ]

    ||| Whether a qualifier as written names the module: its alias in the
    ||| file, or last parts of its path.
    names : (module' : String) -> Subject -> String -> Bool
    names m s x =
      any (\i => show i.path == m && show i.nameAs == x) s.file.mod.imports
      || m == x || isSuffixOf ("." ++ x) m

    ||| In a file that takes the name from the module, each use renamed, its
    ||| qualifier kept.
    useEdits : (module', old, new : String) -> Subject -> List Edit
    useEdits m old new s = mapMaybe one s.written
      where
        root : FC -> Maybe Edit
        root fc = case Span.bounds fc of
          Just ((l, c), (l', c')) =>
            if substr (cast (c' - cast (length old))) (length old) (Subject.lineOf s l') == old
               then Just (MkEdit (l', c' - cast (length old)) (l', c') new) else Nothing
          Nothing => Nothing

        one : (FC, Name) -> Maybe Edit
        one (fc, UN (Basic n)) = if n == old then root fc else Nothing
        one (fc, NS ns (UN (Basic n))) = if n == old && names m s (show ns) then root fc
          else Nothing
        one _ = Nothing

    ||| A file the resolution left out, a program not built, that imports
    ||| the module: taken to use the name from it.
    unresolvedImporter : Resolution -> (module' : String) -> Subject -> Bool
    unresolvedImporter r m t =
      not (any (\rm => rm.path == t.file.path) r.modules)
        && any (\i => show i.path == m) t.file.mod.imports

    ||| Whether the file takes the name from the module, resolved: by its
    ||| path, as programs share the name `Main`.
    takesFrom : Resolution -> (module', old : String) -> Subject -> Bool
    takesFrom r m old s =
      any (\rm => rm.path == s.file.path && any (\u => u.definer == m && u.name == old) rm.uses)
        r.modules

    ||| The rename, one change over every file of the run that takes the
    ||| name, or why it is not made: the module's own edits, and each
    ||| user's.
    plan : Project -> Resolution -> (module', old, new : String) -> Subject -> Either String Change
    plan p r m old new s = do
      let users =
            List.filter
              (\t => show t.file.mod.moduleNS /= m
               && (takesFrom r m old t || unresolvedImporter r m t))
                p.files
          clash = List.filter (\t => new `elem` Finding.joined (map definedBy t.declared)) users
      when (not (null clash)) $
        Left
          ("`" ++ new ++ "` is defined in "
           ++ joinBy ", " (map (\t => show t.file.mod.moduleNS) clash) ++ " already")
      pure (MkChange ((s.file.path, ownEdits old new s) :: List.filter (\(_, es) => not (isNil es))
                        (map (\t => (t.file.path, useEdits m old new t)) users)) [] [])

    candidates : Project -> Subject -> List Refactoring.Candidate
    candidates p s = case (args, p.resolution) of
      ([q, new], Just r) => case split' q of
        Just (m, old) =>
          let defined = Finding.joined (map definedBy s.declared)
              label = "rename " ++ q ++ " to " ++ new
          in if show s.file.mod.moduleNS /= m then []
             else case (old `elem` defined, new `elem` defined) of
               (True, True) =>
                 [Refactoring.candidate label (Left ("`" ++ new ++ "` is defined in its module already"))]
               (True, False) => [Refactoring.candidate label (plan p r m old new s)]
               -- renamed in the module already: the uses left, if any
               (False, True) => case plan p r m old new s of
                 Right ch => if all (\(_, es) => isNil es) ch.edits then []
                   else [Refactoring.candidate label (Right ch)]
                 Left why => [Refactoring.candidate label (Left why)]
               (False, False) => []
        Nothing =>
          [Refactoring.candidate "rename" (Left ("`" ++ q ++ "` is not a name with its module's path"))]
      ([_, _], Nothing) =>
        [Refactoring.candidate "rename" (Left "the modules' uses cannot be resolved: build them first")]
      _ => []
