||| The refactoring `split-module` (`splitModule`): concepts of a module
||| (`Lint.Concept`) moved into a module of their own, and every module that
||| uses them made to import it.
|||
||| It is given the module to make and the concepts to move, and acts on the
||| file whose module has them all. The private concepts only they reach
||| move with them; one that what stays reaches too would have to be
||| exported, and nothing moves. Their declarations move as written, with
||| the comments, pragmas and visibility above them, into the new file,
||| which takes the old module's imports and its `%default`, and imports the
||| old module if what moves uses what stays. The old module imports the new
||| one if what stays uses what moves; if each uses the other, the two would
||| import each other, and nothing moves. Each importer of the old module
||| that names what moves imports the new one too, beside it, and no longer
||| imports the old one if it names nothing that stays there. The package
||| that lists the old module lists the new one after it.
|||
||| What it leaves for after: the imports in order (`order-imports`), the
||| imports a module no longer needs (`prune-imports`, with a check), and the
||| new module's documentation, which only a person can write.
module Lint.Refactor.SplitModule

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Listing
import Lint.Refactor.Project
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.Name.Namespace
import Core.WithData
import Data.List
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Concept
import Lint.Finding
import Lint.Rules
import Lint.Source

%default covering

||| A module's declarations, those that move and those that stay, with the
||| names of each side's concepts: all of them, and those exported.
record Split where
  constructor MkSplit
  moved : List Rules.Declared
  kept : List Rules.Declared
  movedMembers : List String
  keptMembers : List String
  keptOffered : List String

||| `split-module`: given the module to make and the concepts to move, the
||| file whose module has them all split.
export
splitModule : (arguments : List String) -> Refactoring
splitModule args =
  MkRefactoring "split-module"
    ("move concepts of a module into a module of their own (--arg NEW --arg CONCEPT...), its " ++
     "importers rewritten")
    True False candidates
  where
    ||| A file's line ranges, both ends included, joined where they touch,
    ||| overlap, or have nothing but blank lines between them.
    merged : Subject -> List (Int, Int) -> List (Int, Int)
    merged s rs = go (sort rs)
      where
        between : Int -> Int -> Bool
        between b c = all (\l => trim l == "") (Subject.linesBetween s (b + 1) (c - 1))

        go : List (Int, Int) -> List (Int, Int)
        go ((a, b) :: (c, d) :: rest) = if c <= b + 1 || between b c then go ((a, max b d) :: rest)
          else (a, b) :: go ((c, d) :: rest)
        go rs = rs

    ||| A list of names, each in backticks, joined by commas.
    named : List String -> String
    named ns = joinBy ", " (map (\n => "`" ++ n ++ "`") ns)

    ||| The split of a module's declarations by the concepts named.
    namedSplit : Subject -> (names : List String) -> List Concept -> Split
    namedSplit s names cs =
      MkSplit (filter moving s.declared) (filter (not . moving) s.declared)
              (Finding.joined (map (.members) (filter named' cs)))
                (Finding.joined (map (.members) (filter (not . named') cs)))
              (Finding.joined (map (.members) (filter (\c => c.offered && not (named' c)) cs)))
      where
        moving : Rules.Declared -> Bool
        moving d = Concept.ownerIn s.file s.declared d `elem` names

        named' : Concept -> Bool
        named' c = c.name `elem` names

    ||| Whether any of the declarations mentions any of the names.
    mentionsAny : List String -> List Rules.Declared -> Bool
    mentionsAny ns = any (\d => any (`elem` ns) d.mentions)

    ||| The private concepts what moves reaches and what stays does not, which
    ||| move with it, and those both reach, which keep a split from being made.
    movingHelpers : List Concept -> (names : List String) -> (List String, List String)
    movingHelpers cs names =
      let privates = map (.name) (filter (\c => not c.offered && not (c.name `elem` names)) cs)
          kept = map (.name) (filter (\c => c.offered && not (c.name `elem` names)) cs)
          fromMoved = reachedFrom names
          fromKept = reachedFrom kept
      in (filter (\p => contains p fromMoved && not (contains p fromKept)) privates,
          filter (\p => contains p fromMoved && contains p fromKept) privates)
      where
        reachedFrom : List String -> SortedSet String
        reachedFrom ns = foldr (\n, acc => union (Concept.reachable cs n) acc) empty ns

    candidates : Project -> Subject -> List Refactoring.Candidate
    candidates p s = case args of
      (into :: names@(_ :: _)) =>
        let cs = Concept.fileConcepts s.file s.declared in
        if all (\n => any (\c => c.name == n) cs) names
          then
            [Refactoring.candidate ("split " ++ joinBy ", " names ++ " into " ++ into)
              (plan p s into names cs)]
          else []
      _ => []
      where
        -- a declaration's lines, from what is attached above it
        declRange : Subject -> Rules.Declared -> (Int, Int)
        declRange s d = let (a, b) =
                            Span.lineSpan d.decl.fc in
                              (Extent.attachedFrom (Subject.subjectLines s) a, b)

        -- a range taken out, with a blank line after it if one is before
        -- it, or the blank lines before it if nothing but blank lines
        -- follows it
        deletion : Subject -> (Int, Int) -> Edit
        deletion s (a, b) =
          if all (\l => trim l == "") (drop (cast (b + 1)) (Subject.subjectLines s))
            then Edit.deleteLines (blankFrom a) b
          else if trim (Subject.subjectLine s (b + 1)) == ""
            && (a == 0 || trim (Subject.subjectLine s (a - 1)) == "")
            then Edit.deleteLines a (b + 1)
          else Edit.deleteLines a b
          where
            blankFrom : Int -> Int
            blankFrom l = if l > 0 && trim (Subject.subjectLine s (l - 1)) == ""
              then blankFrom (l - 1)
              else l

        importLine : String -> String
        importLine m = "import " ++ m

        -- `import new` after a file's last import
        importAfterLast : Subject -> String -> Edit
        importAfterLast s new =
          case reverse (map (\i => snd (Span.lineSpan i.loc)) s.file.mod.imports) of
          (l :: _) => Edit.insertLines (l + 1) [importLine new]
          [] => Edit.insertLines 0 [importLine new]

        -- the package lists the new module after the old one, the old one
        -- given a comma if it ended the list
        packageEdit : Listing -> (old, new : String) -> Edit
        packageEdit l old new =
          if l.lastInList
            then MkEdit (l.line, 0) (l.line + 1, 0)
              (l.indent ++ old ++ ",\n" ++ l.indent ++ new ++ "\n")
          else Edit.insertLines (l.line + 1) [l.indent ++ new ++ ","]

        -- an importer of the old module that names what moves: it imports
        -- the new one beside it, and no longer the old one if it names
        -- nothing that stays and imports it privately
        importerEdits : (old, new : String) -> (movedMembers, keptOffered : List String) ->
                        Subject -> Maybe (String, List Edit)
        importerEdits old new movedMembers keptOffered t =
          let mentioned = Finding.joined (map (.mentions) t.declared) in
          case find (\i => show i.path == old) t.file.mod.imports of
            Nothing => Nothing
            Just i =>
              if not (any (`elem` movedMembers) mentioned) then Nothing else
                let l = fst (Span.lineSpan i.loc) in
                if not i.reexport && not (any (`elem` keptOffered) mentioned)
                  then Just (t.file.path, [MkEdit (l, 0) (l + 1, 0) (importLine new ++ "\n")])
                  else Just (t.file.path, [Edit.insertLines (l + 1) [importLine new]])

        -- the new module's text: a placeholder for its documentation, its
        -- imports in order, the old module's `%default`, and what moves
        newText : Subject -> (old, new : String) -> List String -> (needsOld : Bool) ->
                  List (Int, Int) -> String
        newText s old new names needsOld ranges =
          let (publics, privates) =
                partition (isPrefixOf "import public")
                  (sort (importLines ++ (if needsOld then [importLine old] else [])))
              defaults = filter (isPrefixOf "%default") (map trim (Subject.subjectLines s))
          in unlines (["||| " ++ named names ++ ", from `" ++ old ++ "`.", "module " ++ new, ""]
                      ++ block publics ++ block privates
                      ++ take 1 defaults ++ [""] ++ body)
          where
            -- lines, then a blank one, if there are any
            block : List String -> List String
            block [] = []
            block ls = ls ++ [""]

            importLines : List String
            importLines =
              map (\i => trim (Subject.subjectLine s (fst (Span.lineSpan i.loc))))
                s.file.mod.imports

            piece : (Int, Int) -> List String
            piece (a, b) = Subject.linesBetween s a b

            body : List String
            body = Finding.joined (intersperse [""] (map piece ranges))

        -- the change that makes the module, or why nothing moves
        plan : Project -> Subject -> (into : String) -> (names : List String) -> List Concept ->
               Either String Change
        plan p s into names cs = do
          let old = show s.file.mod.moduleNS
              (helpers, shared) = movingHelpers cs names
          when (not (null shared)) $
            Left
              ("both what moves and what stays use the private " ++ named shared
               ++ ", which the split would have to export")
          let sp = namedSplit s (names ++ helpers) cs
              needsOld = mentionsAny sp.keptMembers sp.moved
              needsNew = mentionsAny sp.movedMembers sp.kept
          when (any (\d => Span.startColumn d.decl.fc /= 0) sp.moved) $
            Left "a declaration to move is inside a block"
          when (needsOld && needsNew) $
            Left
              ("what moves and what stays refer to each other: the two modules would import " ++
               "each other")
          l <- Listing.packageListing p.packages old into
          let ranges = merged s (map (declRange s) sp.moved)
          pure (MkChange
                  ([ (s.file.path,
                    map (deletion s) ranges ++ (if needsNew then [importAfterLast s into] else [])),
                     (l.package, [packageEdit l old into]) ]
                   ++ mapMaybe (importerEdits old into sp.movedMembers sp.keptOffered) p.files)
                  [(l.newPath, newText s old into names needsOld ranges)] [])
