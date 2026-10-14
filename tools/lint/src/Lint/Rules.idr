||| The rules over one file, on Idris's parse of it: the imports, the
||| declarations with their visibility and documentation, the terms, and the
||| comments. Each rule has a name, which a finding carries and a suppression
||| names. The rules over the import graph are `Lint.Graph`'s.
module Lint.Rules

import Core.Context.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.TT
import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.Zippable
import Idris.Syntax
import Idris.Syntax.Pragmas
import Idris.Syntax.Traversals
import Libraries.Data.WithData
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

||| A rule's finding in a file, where a source position starts.
export
finding : SourceFile -> (rule : String) -> FC -> (subject, message : String) -> Finding
finding f rule fc subject message =
  let (l, c) = position fc in MkFinding rule f.path l c subject message

------------------------------------------------------------------------------
-- What a file's terms refer to

||| The label of the references being collected.
data Collected : Type where

||| An operator where it is written, as symbols or between backticks.
operator : WithFC (OpStr' Name) -> (FC, Name)
operator o = (o.fc, either id id (opNameToEither o.val))

||| The names a term writes where it stands: a reference, an operator, a
||| field projected. Idris's parse holds an operator, and a projection's
||| field, apart from its references; to a reader they are names written.
writes : PTerm -> List (FC, Name)
writes (PRef fc n) = [(fc, n)]
writes (POp _ _ op _) = [operator op]
writes (PPrefixOp _ op _) = [operator op]
writes (PSectionL _ op _) = [operator op]
writes (PSectionR _ _ op) = [operator op]
writes (PPostfixApp _ _ fields) = fields
writes (PPostfixAppPartial _ fields) = fields
writes _ = []

||| What the terms of a file mention: every name it writes, with where, and
||| every `%runElab` in a term.
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
        note r (PRunElab fc _) = update Collected { runElabs $= (fc ::) }
        note r t = update Collected { refs $= (reverse (writes t) ++) }

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
export
facade : SourceFile -> Bool
facade f = all (\d => case d.val of PDirective _ => True; _ => False) f.mod.decls

||| `public-import`: a module imports what it uses, so a public import is for
||| a façade.
publicImport : SourceFile -> List Finding
publicImport f =
  if facade f then [] else
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

------------------------------------------------------------------------------
-- What each declaration defines and mentions

||| A declaration that is not a block of others, with the names it defines
||| and those it mentions (as written, without their namespaces), and, for
||| an implementation, its interface and the names its parameters mention.
public export
record Declared where
  constructor MkDeclared
  decl : PDecl
  defines : List String
  mentions : List String
  implementing : Maybe (String, List String)
  ||| The names an importing module sees: an exported function or type, the
  ||| constructors of a public type, the methods of an exported interface.
  ||| A record's fields are not among them: they are reached through the
  ||| record's namespace.
  visible : List String
  ||| The names mentioned as written without a namespace: where a reader
  ||| must know which of several definitions a name means.
  bare : List String
  ||| The namespace block the declaration is in, by the last part of its
  ||| name, if it is in one.
  namespaced : Maybe String

||| The name a clause defines: the head of its left-hand side.
clauseName : PTerm -> Maybe Name
clauseName (PRef _ n) = Just n
clauseName (PApp _ f _) = clauseName f
clauseName (PAutoApp _ f _) = clauseName f
clauseName (PNamedApp _ f _ _) = clauseName f
clauseName (PWithApp _ f _) = clauseName f
clauseName _ = Nothing

definesOf : PDecl -> List String
definesOf d = case d.val of
  PClaim c => map (nameRoot . (.val) . snd) (forget c.type.val.names)
  PDef (MkPatClause _ lhs _ _ :: _) => maybe [] (\n => [nameRoot n]) (clauseName lhs)
  PDef (MkWithClause _ lhs _ _ _ :: _) => maybe [] (\n => [nameRoot n]) (clauseName lhs)
  PDef (MkImpossible _ lhs :: _) => maybe [] (\n => [nameRoot n]) (clauseName lhs)
  PData _ _ _ (MkPData _ n _ _ _) => [nameRoot n]
  PData _ _ _ (MkPLater _ n _) => [nameRoot n]
  PRecord _ _ _ (MkPRecord n _ _ _ _) => [nameRoot n]
  PRecord _ _ _ (MkPRecordLater n _) => [nameRoot n]
  PInterface _ _ n _ _ _ _ _ => [nameRoot n]
  _ => []

||| The names the terms mention, as written, by Idris's own traversal.
namesWritten : PTerm -> Core (List Name)
namesWritten t = do
  r <- newRef Collected (MkMentions [] [])
  ignore $ mapPTermM (\u => do note u; pure u) t
  m <- get Collected
  pure (map snd m.refs)
  where
    note : {auto r : Ref Collected Mentions} -> PTerm -> Core ()
    note t = update Collected { refs $= (reverse (writes t) ++) }

||| The names the terms mention, without their namespaces.
namesIn : PTerm -> Core (List String)
namesIn t = map nameRoot <$> namesWritten t

||| Whether a name is written without a namespace.
unqualified : Name -> Bool
unqualified (NS _ _) = False
unqualified _ = True

exported : Visibility -> Bool
exported Private = False
exported _ = True

visibleOf : PDecl -> List String
visibleOf d = case d.val of
  PClaim c => if exported c.vis then map (nameRoot . (.val) . snd) (forget c.type.val.names) else []
  PData _ v _ (MkPData _ n _ _ cons) =>
    if exported (collapseDefault v)
       then nameRoot n :: (if collapseDefault v == Public then foldr (\c, rest => map (nameRoot . (.val) . snd) (forget c.val.names) ++ rest) [] cons else [])
       else []
  PData _ v _ (MkPLater _ n _) => if exported (collapseDefault v) then [nameRoot n] else []
  PRecord _ v _ (MkPRecord n _ _ con _) =>
    if exported (collapseDefault v)
       then nameRoot n :: (if collapseDefault v == Public then maybe [] (\c => [nameRoot c.val]) con else [])
       else []
  PRecord _ v _ (MkPRecordLater n _) => if exported (collapseDefault v) then [nameRoot n] else []
  PInterface v _ n _ _ _ _ body =>
    if exported (collapseDefault v)
       then nameRoot n :: foldr (\m, rest => case m.val of
                                                PClaim c => map (nameRoot . (.val) . snd) (forget c.type.val.names) ++ rest
                                                _ => rest) [] body
       else []
  _ => []

isBlock : PDecl -> Bool
isBlock d = case d.val of
  PMutual _ => True
  PNamespace _ _ => True
  PParameters _ _ => True
  PUsing _ _ => True
  _ => False

startLine : PDecl -> Int
startLine d = fst (position d.fc)

||| The last part of a dotted name.
export
lastPart : String -> String
lastPart m = maybe m id (last' (forget (split (== '.') m)))

||| The declarations of a file that are not blocks of others, in the order
||| they are written, each with what it defines and mentions.
export
declared : SourceFile -> IO (List Declared)
declared f = coreRun (traverse one leaves) (\_ => pure []) pure
  where
    -- each declaration that is not a block of others, with the namespace
    -- block it is in
    leavesIn : Maybe String -> List PDecl -> List (Maybe String, PDecl)
    leavesIn ns = foldr (\d, rest => here d ++ rest) []
      where
        here : PDecl -> List (Maybe String, PDecl)
        here d = case d.val of
          PNamespace n ds => leavesIn (Just (lastPart (show n))) ds
          PMutual ds => leavesIn ns ds
          PParameters _ ds => leavesIn ns ds
          PUsing _ ds => leavesIn ns ds
          _ => [(ns, d)]

    leaves : List (Maybe String, PDecl)
    leaves = sortBy (\a, b => compare (startLine (snd a)) (startLine (snd b))) (leavesIn Nothing f.mod.decls)

    one : (Maybe String, PDecl) -> Core Declared
    one (ns, d) = do
      written <- namesWritten (PQuoteDecl EmptyFC [d])
      let ms = map nameRoot written
          bareNames = map nameRoot (filter unqualified written)
      impl <- case d.val of
        PImplementation _ _ _ _ _ iface params _ _ _ => do
          ps <- traverse namesIn params
          pure (Just (nameRoot iface, foldr (++) [] ps))
        _ => pure Nothing
      pure (MkDeclared d (definesOf d) ms impl (visibleOf d) bareNames ns)

||| The types a file defines (data types and records), by name.
export
typesOf : List Declared -> List String
typesOf ds = foldr (\d, rest => case d.decl.val of
                                   PData _ _ _ _ => d.defines ++ rest
                                   PRecord _ _ _ _ => d.defines ++ rest
                                   _ => rest) [] ds

||| An implementation and a type of its file that its parameters name: where
||| each is in the file's declarations, and whether nothing stands between
||| them but the type's family, the first that does if something does. The
||| family: what the type's definition and all its implementations name (a
||| type defined with it in a mutual block, the helpers they use), what those
||| name in turn, and the implementations for any of them, which the
||| type's implementations use without naming them.
public export
record Adjacency where
  constructor MkAdjacency
  impl : Declared
  type : String
  intruder : Maybe Declared

||| `implementation-adjacent`, strict: an implementation for a type of its
||| file follows the type with nothing between them but the type's other
||| implementations and what they use, which Idris puts above them.
export
adjacency : List Declared -> List Adjacency
adjacency ds =
  let indexed = zip [0 .. length ds] ds
      types = typesOf ds
  in foldr (\(j, d), rest => case d.implementing of
       Nothing => rest
       Just (_, params) =>
         mapMaybe (\t => map (\i => MkAdjacency d t (intruder indexed i j t)) (typeAt indexed t)) (filter (`elem` params) types) ++ rest)
     [] indexed
  where
    typeAt : List (Nat, Declared) -> String -> Maybe Nat
    typeAt xs t = foldr (\(k, d), rest => if isType d && (t `elem` d.defines) then Just k else rest) Nothing xs
      where
        isType : Declared -> Bool
        isType d = case d.decl.val of
          PData _ _ _ _ => True
          PRecord _ _ _ _ => True
          _ => False

    implementsFor : String -> Declared -> Bool
    implementsFor t d = case d.implementing of
      Just (_, ps) => t `elem` ps
      Nothing => False

    ignorable : Declared -> Bool
    ignorable d = case d.decl.val of
      PDirective _ => True
      PFixity _ => True
      _ => False

    -- the names of the type's family: those its definition and all its
    -- implementations mention, and in turn those the declarations they
    -- name, or implementations for them, mention, to a fixed point
    used : Declared -> List Declared -> List Declared -> List String
    used ty impls others = go (foldr (\d, rest => d.mentions ++ rest) ty.mentions impls) others
      where
        named : List String -> Declared -> Bool
        named names d = any (`elem` names) d.defines || maybe False (\ip => any (`elem` names) (snd ip)) d.implementing

        go : List String -> List Declared -> List String
        go names rest =
          let more = filter (\d => named names d && not (all (`elem` names) d.mentions)) rest in
          case more of
            [] => names
            -- lint: allow trust-escape: each round takes declarations out of those still unfinished, of which there are finitely many
            _ => assert_total (go (foldr (\d, acc => d.mentions ++ acc) names more) rest)

    -- the declarations strictly after position lo and before hi
    within : Nat -> Nat -> List (Nat, Declared) -> List Declared
    within lo hi = foldr (\(k, d), rest => if k > lo && k < hi then d :: rest else rest) []

    at : List (Nat, Declared) -> Nat -> Maybe Declared
    at xs i = foldr (\(k, d), rest => if k == i then Just d else rest) Nothing xs

    intruder : List (Nat, Declared) -> Nat -> Nat -> String -> Maybe Declared
    intruder xs i j t =
      let between = within i j xs
          everything = map snd xs
          impls = filter (implementsFor t) everything
          names = maybe [] (\ty => used ty impls everything) (at xs i)
          family = \d => implementsFor t d || ignorable d || any (`elem` names) d.defines
                        || maybe False (\ip => any (`elem` names) (snd ip)) d.implementing
      in find (not . family) between

implementationAdjacent : SourceFile -> List Declared -> List Finding
implementationAdjacent f ds =
  mapMaybe one (adjacency ds)
  where
    intruderName : Declared -> String
    intruderName d = case d.defines of
      (n :: _) => n
      [] => case d.implementing of
        Just (i, ps) => i ++ " " ++ fastConcat (intersperse " " (take 1 ps))
        Nothing => "a declaration"

    one : Adjacency -> Maybe Finding
    one a = flip map a.intruder $ \d =>
      let iface = maybe "" fst a.impl.implementing in
      finding f "implementation-adjacent" a.impl.decl.fc (iface ++ " " ++ a.type)
        ("`" ++ iface ++ " " ++ a.type ++ "` stands apart from `" ++ a.type ++ "`: `" ++ intruderName d
         ++ "` is between them, neither one of its implementations nor something they use")

||| `module-name`, a warning: a module is named after a key symbol it
||| defines (a type, a function), so that a reader looking for `Enc` opens
||| `Enc.idr`. A façade, which defines nothing, is exempt.
export
namedAfterSymbol : SourceFile -> List Declared -> Bool
namedAfterSymbol f ds =
  facade f || any (\n => toLower n == toLower (lastPart (show f.mod.moduleNS))) (foldr (\d, rest => d.defines ++ rest) [] ds)

||| An overload of its type: a declaration in a namespace block named after a
||| type its own signature or body names, as `area` in `namespace Circle`.
||| Overloads of one concept across types are how Idris writes it, and are
||| not two meanings of a name.
export
typedOverload : Declared -> Bool
typedOverload d = maybe False (\ns => ns `elem` d.mentions) d.namespaced

||| Whether a declaration is a private function at the top of its module,
||| not in a namespace block, that could be anywhere else: a function
||| declared `%extern` or `%foreign` can only be at the top.
privateAtTop : Declared -> Bool
privateAtTop d = isNothing d.namespaced && case d.decl.val of
  PClaim c => not (exported c.vis) && not (any foreignOpt c.opts)
  _ => False
  where
    foreignOpt : PFnOpt -> Bool
    foreignOpt (PForeign _) = True
    foreignOpt (IFnOpt ExternFn) = True
    foreignOpt _ = False

||| How many functions a declaration keeps local: those declared in the
||| `where` blocks of its clauses, at any depth.
localFunctions : PDecl -> Nat
localFunctions d = case d.val of
  PDef cls => sum (map clause cls)
  _ => 0
  where
    inWhere : PDecl -> Nat
    inWhere w = (case w.val of PClaim _ => 1; _ => 0) + localFunctions w

    clause : PClause -> Nat
    clause (MkPatClause _ _ _ wh) = sum (map inWhere wh)
    clause (MkWithClause _ _ _ _ cs) = sum (map clause cs)
    clause (MkImpossible _ _) = 0

||| The private functions of a module, for the score: those at its top used
||| by exactly one other declaration, with that one, which a reader carries
||| to the end of the module; and how many are scoped, which a reader can
||| forget when their block ends: local to a function (`where`), or private
||| to a namespace block.
export
helpers : List Declared -> (List (Declared, Declared), Nat)
helpers ds =
  let atTop = filter privateAtTop ds
      single = mapMaybe (\h => case users h of [u] => Just (h, u); _ => Nothing) atTop
      scoped = length (filter (\d => isJust d.namespaced && isPrivateClaim d) ds)
               + sum (map (localFunctions . (.decl)) ds)
  in (single, scoped)
  where
    isPrivateClaim : Declared -> Bool
    isPrivateClaim d = case d.decl.val of
      PClaim c => not (exported c.vis)
      _ => False

    -- the declarations that mention a function, those defining it aside
    users : Declared -> List Declared
    users h = filter (\d => not (any (`elem` h.defines) d.defines) && any (`elem` h.defines) d.mentions) ds

moduleName' : SourceFile -> List Declared -> List Finding
moduleName' f ds =
  if namedAfterSymbol f ds then [] else
    [finding f "module-name" f.mod.headerLoc (show f.mod.moduleNS)
       ("`" ++ show f.mod.moduleNS ++ "` is named after nothing it defines: a reader looks a symbol up by its module's name")]

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
fileRules : SourceFile -> Mentions -> List Declared -> List Finding
fileRules f ms ds =
  importOrder f ++ publicImport f ++ defaultTotality f ++ elabReflection f ms
  ++ trustEscape f ms ++ citesPlan f ++ todo f ++ headerComment f
  ++ implementationAdjacent f ds ++ moduleName' f ds

||| How a finding of each rule counts: an error fails the gate, a warning
||| is advice, printed when asked for.
export
isWarning : (rule : String) -> Bool
isWarning rule = rule == "module-name" || rule == "same-name" || rule == "list-accumulation"

||| The names of every rule, those over the graph and over the resolution
||| included.
export
ruleNames : List String
ruleNames =
  [ "import-order", "public-import", "default-totality", "elab-reflection"
  , "trust-escape", "cites-plan", "todo", "header-comment", "implementation-adjacent", "module-name"
  , "layering", "syscall", "same-name", "import-unused", "import-indirect", "list-accumulation", "generic-export"
  , "parent-unique", "import-alias" ]
