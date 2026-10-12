||| The rules over one file, on Idris's parse of it: the imports, the
||| declarations with their visibility and documentation, the terms, and the
||| comments. Each rule has a name, which a finding carries and a suppression
||| names. The rules over the import graph are `Lint.Graph`'s.
module Lint.Rules

import Core.Core
import Core.FC
import Core.Name
import Core.TT
import Data.List
import Data.List1
import Data.String
import Idris.Syntax
import Idris.Syntax.Pragmas
import Idris.Syntax.Traversals
import Libraries.Data.WithDefault
import Lint.Finding
import Lint.Source
import TTImp.TTImp

%default covering

||| Where a source position starts.
position : FC -> (Int, Int)
position (MkFC _ s _) = s
position (MkVirtualFC _ s _) = s
position EmptyFC = (0, 0)

finding : SourceFile -> (rule : String) -> FC -> (subject, message : String) -> Finding
finding f rule fc subject message =
  let (l, c) = position fc in MkFinding rule f.path l c subject message

------------------------------------------------------------------------------
-- What a file's terms refer to

||| The label of the references being collected.
data Collected : Type where

||| What the terms of a file mention: every name it refers to, with where,
||| and every `%runElab` in a term.
public export
record Mentions where
  constructor MkMentions
  refs : List (FC, Name)
  runElabs : List FC

||| The mentions of a module's declarations: Idris's own traversal of terms,
||| over the declarations quoted as one term.
export
mentions : List PDecl -> IO Mentions
mentions ds = coreRun walk (\_ => pure (MkMentions [] [])) pure
  where
    walk : Core Mentions
    walk = do
      r <- newRef Collected (MkMentions [] [])
      ignore $ mapPTermM (\t => do note r t; pure t) (PQuoteDecl EmptyFC ds)
      m <- get Collected
      pure ({ refs $= reverse, runElabs $= reverse } m)
      where
        note : Ref Collected Mentions -> PTerm -> Core ()
        note r (PRef fc n) = update Collected { refs $= ((fc, n) ::) }
        note r (PRunElab fc _) = update Collected { runElabs $= (fc ::) }
        note r _ = pure ()

------------------------------------------------------------------------------
-- Imports

||| A module's name as Idris writes it.
moduleName : ModuleIdent -> String
moduleName = show

||| `import-order`: the public imports first, then the private ones, each in
||| alphabetical order, as a reader sorts: letters before their case, so
||| `Runtime.Object` comes before `Runtime.OS`. The first import out of its
||| place is reported.
importOrder : SourceFile -> List Finding
importOrder f =
  let is = f.mod.imports
      key = \i => (not i.reexport, toLower (moduleName i.path), moduleName i.path)
      want = sortBy (\a, b => compare (key a) (key b)) is
  in case find (\(a, b) => key a /= key b) (zip is want) of
       Nothing => []
       Just (a, b) =>
         [finding f "import-order" a.loc (moduleName a.path)
            ("`" ++ moduleName b.path ++ "` comes here: the public imports first, then the private ones, each alphabetical")]

||| A façade: a module that declares nothing, only re-exports.
isFacade : SourceFile -> Bool
isFacade f = all directive f.mod.decls
  where
    directive : PDecl -> Bool
    directive d = case d.val of
      PDirective _ => True
      _ => False

||| `public-import`: a module imports what it uses, so a public import is for
||| a façade.
publicImport : SourceFile -> List Finding
publicImport f =
  if isFacade f then [] else
    [ finding f "public-import" i.loc (moduleName i.path)
        ("`" ++ moduleName i.path ++ "` imported publicly: a module that uses it imports it")
    | i <- f.mod.imports, i.reexport ]

------------------------------------------------------------------------------
-- Declarations

||| The declarations of a module, those in blocks included: mutual,
||| namespaces, parameters and `using` blocks. A failing block is not code.
export
declarations : List PDecl -> List PDecl
declarations = foldr (\d, rest => d :: inner d ++ rest) []
  where
    inner : PDecl -> List PDecl
    inner d = case d.val of
      PMutual ds => declarations ds
      PNamespace _ ds => declarations ds
      PParameters _ ds => declarations ds
      PUsing _ ds => declarations ds
      _ => []

||| `default-totality`: every module says how total its functions are by
||| default.
defaultTotality : SourceFile -> List Finding
defaultTotality f =
  if any isDefault f.mod.decls then [] else
    [finding f "default-totality" f.mod.headerLoc (show f.mod.moduleNS) "no `%default` directive"]
  where
    isDefault : PDecl -> Bool
    isDefault d = case d.val of
      PDirective (DefaultTotality _) => True
      _ => False

||| `elab-reflection`: no elaborator reflection until the compiler compiles
||| itself natively: no `%runElab`, no `%macro`, no extension.
elabReflection : SourceFile -> Mentions -> List Finding
elabReflection f ms =
  mapMaybe decl (declarations f.mod.decls)
  ++ [ finding f "elab-reflection" fc "%runElab" "`%runElab`" | fc <- ms.runElabs ]
  where
    isMacro : PFnOpt -> Bool
    isMacro (IFnOpt TTImp.TTImp.Macro) = True
    isMacro _ = False

    decl : PDecl -> Maybe Finding
    decl d = case d.val of
      PDirective (Extension ElabReflection) => Just (finding f "elab-reflection" d.fc "%language" "`%language ElabReflection`")
      PRunElabDecl _ => Just (finding f "elab-reflection" d.fc "%runElab" "`%runElab` declaration")
      PClaim c => if any isMacro c.opts
                    then Just (finding f "elab-reflection" d.fc "%macro" "`%macro` function")
                    else Nothing
      _ => Nothing

||| The functions that leave what the typechecker proves: each use says why
||| it is sound.
escapes : List String
escapes = ["assert_total", "assert_smaller", "believe_me", "really_believe_me", "idris_crash", "unsafePerformIO"]

||| `trust-escape`: a use of one of `escapes`, each to be suppressed with its
||| reason.
trustEscape : SourceFile -> Mentions -> List Finding
trustEscape f ms =
  [ finding f "trust-escape" fc (nameRoot n) ("`" ++ nameRoot n ++ "`: say why it is sound")
  | (fc, n) <- ms.refs, nameRoot n `elem` escapes ]

------------------------------------------------------------------------------
-- Comments

||| A word of a text, its letters, digits, `-` and `_` kept together.
words' : String -> List String
words' s = forget (split (\c => not (isAlphaNum c || c == '-' || c == '_' || c == '/' || c == '.')) s)

||| The prefixes of the plans' items: the queue's, the Idris ledger's, the
||| fork's ledger's.
planPrefixes : List String
planPrefixes = ["PQ-", "IL-", "FL-"]

||| A plan cited: `PQ-`, `IL-` or `FL-` and three digits, or a document of
||| the plans (a path under `docs/`, a `.md` file).
citation : String -> Maybe String
citation w =
  if any (\p => isPrefixOf p w && length w >= 6 && all isDigit (unpack (substr 3 3 w))) planPrefixes
     then Just (substr 0 6 w)
  else if (isInfixOf "docs/" w && not (isSuffixOf "docs/" w)) || (isSuffixOf ".md" w && length w > 3) then Just w
  else Nothing

||| `cites-plan`: the code is the specification, so it cites no plan.
citesPlan : SourceFile -> List Finding
citesPlan f =
  [ MkFinding "cites-plan" f.path c.line c.col w ("cites `" ++ w ++ "`: the code states what it needs")
  | c <- f.comments, w <- mapMaybe citation (words' c.text) ]

||| The words that mark work left open.
openWork : List String
openWork = ["TODO", "FIXME", "XXX"]

||| `todo`: open work is planned, not left in the code.
todo : SourceFile -> List Finding
todo f =
  [ MkFinding "todo" f.path c.line c.col w ("`" ++ w ++ "`: open work belongs in the plans")
  | c <- f.comments, w <- words' c.text, w `elem` openWork ]

||| `header-comment`: a file says what it is before its first import or
||| declaration: in the module's documentation, or in a comment.
headerComment : SourceFile -> List Finding
headerComment f =
  let firstItem = foldl min 2147483647 (map (fst . position . (.loc)) f.mod.imports ++ map (fst . position . (.fc)) f.mod.decls)
  in if f.mod.documentation /= "" || any (\c => c.line < firstItem) f.comments then [] else
       [MkFinding "header-comment" f.path 0 0 (show f.mod.moduleNS) "no comment says what the file is before its first import or declaration"]

------------------------------------------------------------------------------
-- All of them

||| The rules over a program's file (a test, an example): what it says about
||| itself and the order of its imports; the rules of the product's code do
||| not bind it.
export
programRules : SourceFile -> List Finding
programRules f = importOrder f ++ citesPlan f ++ todo f ++ headerComment f

||| The rules over one file of the product.
export
fileRules : SourceFile -> Mentions -> List Finding
fileRules f ms =
  importOrder f ++ publicImport f ++ defaultTotality f ++ elabReflection f ms
  ++ trustEscape f ms ++ citesPlan f ++ todo f ++ headerComment f

||| The names of every rule, those over the graph included.
export
ruleNames : List String
ruleNames =
  [ "import-order", "public-import", "default-totality", "elab-reflection"
  , "trust-escape", "cites-plan", "todo", "header-comment", "layering", "syscall" ]
