||| The refactoring `scope-helpers` (`scopeHelpers`): a private function at
||| the top of a module that one other declaration uses moves into the
||| `where` block of the clause of that declaration that uses it.
|||
||| A reader then forgets it with the clause, instead of carrying it to the
||| end of the module. It moves with its comments and pragmas and with any
||| helpers already moved into it. It moves only where it means the same:
||| its user is a function, or a method of an implementation; one clause of
||| the user uses it; no name its clauses refer to, beyond its type's, is
||| bound as a value where it goes, by the clause's left-hand side, the
||| clause's `where` block or a `parameters` block it does not share, and
||| neither is its own name; and it is one piece of text. A name of its
||| type bound there, a variable bound implicitly (`a`) or by an implicit
||| binder of its own (`{vars : _}`), is renamed with a prime (`a'`,
||| `vars'`), so the helper stays as general as it was. A helper whose own
||| helpers have not moved yet waits for them, so a chain moves from its
||| end, each part into the one that uses it.
module Lint.Refactor.ScopeHelpers

import Lint.Refactor.Binders
import Lint.Refactor.Change
import Lint.Refactor.Constraints
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Free
import Lint.Refactor.NamedArguments
import Lint.Refactor.ParameterBlock
import Lint.Refactor.Refactoring
import Lint.Refactor.Span
import Lint.Refactor.Subject
import Lint.Refactor.Where

import Core.FC
import Core.Name
import Core.WithData
import Data.Either
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source

%default covering


||| `scope-helpers`: each single-use private function at the top of a module
||| moved into its user's `where` block, its own helpers first.
export
scopeHelpers : Refactoring
scopeHelpers = Refactoring.fileRefactoring "scope-helpers"
  "move each private function one other declaration uses into that one's `where` block"
  candidates
  where
    ||| The names the module defines: globals, never variables of a type.
    globalsOf : Subject -> SortedSet String
    globalsOf s = fromList (foldr (\d, rest => d.defines ++ rest) [] s.declared)

    ||| The change that moves a helper into the clause of its user that uses it,
    ||| or why it stays; and the one to prefer, if it differs: the helper at
    ||| its user's own type variables, not renamed, and without the
    ||| constraints its user has, which only the type checker can judge,
    ||| since the helper may be used at other types than its user's.
    plan : Subject -> (helper, user : Rules.Declared) -> Either String (Change, Maybe Change)
    plan s h u = do
      (cls, aroundUser) <- clausesOf s u
      cl <- clauseUsing cls
      extent <- Extent.extentOf s h
      (aroundBlock, lifted, userBlock, ownBlock) <- placement extent cl
      let values = union (boundOf cl) (union aroundBlock (whereNames cl))
          own = maybe empty (.names) ownBlock
      noCapture values aroundUser
      (text, calls) <- adjust cl (union values aroundUser) lifted userBlock own extent
      insert <- Where.intoWhere (Subject.linesOf s) cl h.defines (helperFree s h) extent.column text
      let safe = Change.inFile s.file.path ([insert, Extent.cut (Subject.linesOf s) extent] ++ calls)
          preferred = do
            (text', calls') <- eitherToMaybe (adjust cl values lifted userBlock own extent)
            if text' == text then Nothing else do
              insert' <- eitherToMaybe
                (Where.intoWhere (Subject.linesOf s) cl h.defines (helperFree s h) extent.column text')
              Just (Change.inFile s.file.path ([insert', Extent.cut (Subject.linesOf s) extent] ++ calls'))
      pure (safe, preferred)
      where
        -- the constraints the user has, as written: its claim's, or its
        -- implementation's
        userConstraints : List String
        userConstraints = case u.decl.val of
          PImplementation _ _ _ _ cs _ _ _ _ _ =>
            foldr (\c, rest => Constraints.writtenAs (Subject.linesOf s) (snd c) ++ rest) [] cs
          _ => foldr (\d, rest => case d.decl.val of
                                     PClaim c => if any (`elem` u.defines) d.defines
                                                   then Constraints.constraintsOf (Subject.linesOf s) c.type.val.type
                                                     ++ rest else rest
                                     _ => rest) [] s.declared

        -- the one clause of the user that uses the helper
        clauseUsing : List PClause -> Either String PClause
        clauseUsing cls = case filter (\cl => any (\n => contains n (Free.inClause cl)) h.defines) cls of
          [cl] => Right cl
          [] => Left ("it is unused: `" ++ Refactoring.labelOf u ++ "` mentions only a name of its own")
          more => Left (show (length more) ++ " clauses of `" ++ Refactoring.labelOf u ++ "` use it")

        -- the names a `parameters` block binds around the clause and not
        -- around the helper; the block the helper leaves, if it does, whose
        -- parameters it then takes itself; and the user's block
        placement : Extent -> PClause ->
                    Either String
                    (SortedSet String, Maybe ParameterBlock, Maybe ParameterBlock,
                     Maybe ParameterBlock)
        placement extent cl =
          let blocks = ParameterBlock.parameterBlocks (Subject.linesOf s) s.file.mod.decls in
          case (ParameterBlock.blockAt blocks (fst (Span.lineSpan h.decl.fc)),
                ParameterBlock.blockAt blocks (fst (Span.lineSpan (Where.clauseLoc cl)))) of
            (Nothing, Nothing) => Right (empty, Nothing, Nothing, Nothing)
            (Nothing, Just b) => Right (b.names, Nothing, Just b, Nothing)
            (Just a, Just b) =>
              if ParameterBlock.sameParameters a b then Right (empty, Nothing, Just b, Just a)
                else Left "its user is in a `parameters` block of other parameters"
            (Just a, Nothing) =>
              if ParameterBlock.implicitOnly a then Right (empty, Just a, Nothing, Just a)
              else Left
                "it would leave a `parameters` block whose explicit parameters its calls pass"

        -- the lines of a declaration's source
        sourceOf : Rules.Declared -> List String
        sourceOf d = let (a, b) =
                           Span.lineSpan d.decl.fc in List.take (cast (b - a + 1))
                             (List.drop (cast a) (Subject.linesOf s))

        -- the auto-implicits around the clause: its user's type's, and its
        -- user's `parameters` block's
        autosAround : Maybe ParameterBlock -> List (String, String)
        autosAround userBlock =
          let claims = filter (\d => case d.decl.val of
                                        PClaim _ => any (`elem` u.defines) d.defines
                                        _ => False) s.declared
              ofClaims =
                foldr (\d, rest => map snd (Binders.binderGroups (joinBy "\n" (sourceOf d))) ++ rest) []
                  claims
          in mapMaybe Binders.autoBinder (ofClaims ++ maybe [] (.binders) userBlock)

        -- the helper as it must read where it goes, from its source: each
        -- variable its types leave free that is bound there renamed afresh
        -- where it occurs, so that it is bound implicitly as it was at the
        -- top; an auto-implicit the clause already has, as written, dropped,
        -- so that search finds one; and the parameters of a block it leaves
        -- taken. With it, the edits to the user's clause: an implicit binder
        -- renamed is renamed where the clause's calls name it, `{enc}`
        -- becoming `{enc' = enc}`
        adjust : PClause -> (bound : SortedSet String) ->
                 (lifted, userBlock : Maybe ParameterBlock) -> (ownParameters : SortedSet String) ->
                 Extent -> Either String (List String, List Edit)
        adjust cl bound lifted userBlock ownParameters extent = do
          let (renames, binders) = renamesFor bound ownParameters
              every = renames ++ binders
          when (any (\(_, _, ps) => (-1, -1) `elem` ps) every) $
            Left "a name it must rename occurs where it cannot be renamed"
          let own = foldr (\b, rest => calls (clausesOfHelper) b ++ rest) [] binders
              ownShort = shortOnes own
              binders' =
                map (\(n, to, ps) => (n, to, filter (\p => not (p `elem` ownShort)) ps)) binders
              ownEdits = map (\(p, _, (n, to)) => nameEdit p n to) own
          renamed <- maybe (Left "its renames overlap") Right
            (Edit.apply (foldr (\r, rest => renameEdits r ++ rest) ownEdits (renames ++ binders'))
             s.text)
          claimed' <- claimAdjusted (lines renamed) (autosAround userBlock)
            (map (\(n, _, _) => n) every)
          let claimed = withoutShared (map (\(n, _, _) => n) every) claimed'
          let (cs, ce) = Span.lineSpan h.decl.fc
              userEdits =
                map (\(p, short, (n, to)) => nameEdit p n (if short then to ++ " = " ++ n else to))
                              (foldr (\b, rest => calls [cl] b ++ rest) [] binders)
          pure (splice (Extent.indexIn extent cs) (ce - cs + 1) claimed (Extent.textOf (lines renamed) extent),
                userEdits)
          where
            clausesOfHelper : List PClause
            clausesOfHelper = foldr (\d, rest => case d.decl.val of
                                                   PDef cs => cs ++ rest
                                                   _ => rest) [] (Extent.definitionsOf s h)

            -- the calls of the helper among clauses that name a binder:
            -- where the name is, whether it is written short, and the rename
            calls : List PClause -> (String, String, List (Int, Int)) ->
                    List ((Int, Int), Bool, (String, String))
            calls cls (n, to, _) =
              let occ = Free.allOf (map Free.clauseAt cls) in
              foldr (\f,
                rest =>
                  foldr (\p,
                    more =>
                      map (\(q, short) => (q, short, (n, to))) (NamedArguments.namedArguments (Subject.linesOf s) p f n)
                         ++ more)
                                       rest (fromMaybe [] (lookup f occ))) [] h.defines

            -- the places of the names written short, whose value is renamed
            -- with them
            shortOnes : List ((Int, Int), Bool, (String, String)) -> List (Int, Int)
            shortOnes xs = map (\(p, _, _) => p) (List.filter (\(_, short, _) => short) xs)

            nameEdit : (Int, Int) -> String -> String -> Edit
            nameEdit (l, c) n text = MkEdit (l, c) (l, c + cast (length n)) text

            clausesIn : Rules.Declared -> List PClause
            clausesIn d = case d.decl.val of
              PDef cs => cs
              _ => []

            claimType : Rules.Declared -> Maybe PTerm
            claimType c = case c.decl.val of
              PClaim cd => Just cd.type.val.type
              _ => Nothing

            -- the claim's lines without each constraint the user has as
            -- written, unless it names a variable renamed: search finds the
            -- user's
            withoutShared : (renamed : List String) -> List String -> List String
            withoutShared renamed ls =
              let theirs = map Constraints.tidy userConstraints
                  mine = maybe [] (Constraints.constraintsOf (Subject.linesOf s)) (claimType h)
                  dropped =
                    List.filter
                      (\w => elem (Constraints.tidy w) theirs
                       && not (any (\n => elem n renamed) (identifiers w)))
                        mine
              in lines (foldl (\t, w => Constraints.withoutConstraint w t) (joinBy "\n" ls) dropped)
              where
                identifiers : String -> List String
                identifiers w =
                  Data.List1.forget
                    (Data.String.split (\ch => not (isAlphaNum ch || ch == '_' || ch == '\'')) w)

            -- a name not bound where the helper goes, nor used by it, nor the
            -- module's: the name with primes
            freshFor : SortedSet String -> String -> String
            freshFor avoid n = go (n ++ "'")
              where
                go : String -> String
                go c = if contains c avoid then go (c ++ "'") else c

            -- each name to rename, what to, and where it occurs: the
            -- variables the helper's type leaves free that are bound where it
            -- goes, at their occurrences in its type and its clauses; and so
            -- for each claim within it whose type leaves free such a variable
            -- that no scope around it within the helper binds. A name its
            -- type binds by an implicit binder of its own, which its clauses
            -- have in scope, is renamed too if it is bound where it goes:
            -- Idris confuses the two in the case blocks around them. It is
            -- renamed at its binder, under it, and in its clauses, unless a
            -- clause binds it on its left-hand side. The parameters of the
            -- block the helper is in are no implicits: they mean the same
            -- where it goes, or become its own binders; nor is an
            -- auto-implicit the clause has, which the helper drops
            renamesFor : SortedSet String -> (taken : SortedSet String) ->
                         (List (String, String, List (Int, Int)),
                          List (String, String, List (Int, Int)))
            renamesFor bound taken =
              let globals = globalsOf s
                  defs = foldr (\d, rest => clausesIn d ++ rest) [] (Extent.definitionsOf s h)
                  ty = claimType h
                  topOcc = Free.allOf (maybe empty Free.occurrences ty :: map Free.clauseAt defs)
                  avoid =
                    union bound (union globals (union (Free.namesOf topOcc) (maybe empty Free.typeNames ty)))
                  topVars = maybe empty (\t => intersection (Free.free t) (Free.typeVariables globals t)) ty
                  top = map (\n => (n, freshFor avoid n, fromMaybe [] (lookup n topOcc)))
                            (filter (\n => contains n bound && not (contains n taken))
                              (Prelude.toList topVars))
                  shadowed =
                    maybe [] (\t => map (\n => (n, freshFor avoid n, binderRename defs t n))
                                                 (filter
                                                   (\n => contains n bound && not (contains n taken)
                                                    && not (contains n autos))
                                                         (Prelude.toList (Free.implicitBinders t)))) ty
                  inner = Free.claimsWithin globals (union taken (maybe empty Free.typeNames ty)) defs
                  nested = foldr (\ic, rest => innerRenames avoid ic ++ rest) [] inner
              in (top ++ nested, shadowed)
              where
                autos : SortedSet String
                autos =
                  fromList
                    (mapMaybe (\g => map fst (Binders.autoBinder (snd g)))
                     (Binders.binderGroups (joinBy "\n" (sourceOf h))))

                binderRename : List PClause -> PTerm -> String -> List (Int, Int)
                binderRename defs t n =
                  if any (\cl => contains n (Free.boundBy (Rules.lhsOf cl))) defs then [(-1, -1)]
                  else Free.implicitSites n t ++ fromMaybe [] (lookup n (Free.allOf (map Free.clauseAt defs)))


                innerRenames : SortedSet String -> Free.InnerClaim ->
                               List (String, String, List (Int, Int))
                innerRenames avoid ic =
                  let occ = Free.allOf (Free.occurrences ic.type :: map Free.clauseAt ic.clauses) in
                  map
                    (\n =>
                      the (String, String, List (Int, Int))
                     (n, freshFor avoid n, fromMaybe [] (lookup n occ)))
                      (filter (\n => contains n bound && not (contains n ic.around))
                        (Prelude.toList ic.variables))

            -- a rename at each place; a named argument written short, `{n}`
            -- for `{n = n}`, keeps its name: `{n = n'}`
            renameEdits : (String, String, List (Int, Int)) -> List Edit
            renameEdits (n, to, ps) =
              map
                (\(l, c) =>
                  MkEdit (l, c) (l, c + cast (length n))
                 (if short l c then n ++ " = " ++ to else to))
                  ps
              where
                short : Int -> Int -> Bool
                short l c =
                  let line = fromMaybe "" (head' (List.drop (cast l) (Subject.linesOf s)))
                      before = trim (substr 0 (cast c) line)
                      after = trim (substr (cast c + length n) (length line) line)
                  in isSuffixOf "{" before && isPrefixOf "}" after

            -- the binders of the block the helper leaves before its type,
            -- those the clause does not provide: a name it binds, or an
            -- auto-implicit it has as written
            lifting : List (String, String) -> List String -> List String
            lifting around ls = case lifted of
              Nothing => ls
              Just b => let (comments, rest) = span comment ls in
                        case rest of
                          (sig :: more) => comments ++ Binders.prefixType (ParameterBlock.binderPrefix provided b) sig
                            :: more
                          [] => ls
              where
                provided : String -> Bool
                provided g = maybe False (\o => o `elem` around) (Binders.autoBinder g)
                  || maybe False (\n => contains n bound) (Binders.binderName g)

                comment : String -> Bool
                comment l = let t = trim l in isPrefixOf "|||" t || isPrefixOf "--" t

            -- the helper's claim, from the renamed lines: a shared
            -- auto-implicit dropped, and the binders of a block it leaves
            -- put before its type, on the line the type starts on, past its
            -- comments
            claimAdjusted : List String -> List (String, String) -> (renamed : List String) ->
                            Either String (List String)
            claimAdjusted ls around renamed =
              let (cs, ce) = Span.lineSpan h.decl.fc
                  claimText = joinBy "\n" (List.take (cast (ce - cs + 1)) (List.drop (cast cs) ls))
                  own = mapMaybe ownAuto (Binders.binderGroups claimText)
              in case List.filter clashing own of
                   (o :: _) =>
                     Left
                       ("it takes an auto-implicit its user has under another name: `" ++ fst o
                        ++ "`")
                   [] =>
                     Right
                       (lifting around
                         (lines
                           (foldl (\t, o => Binders.withoutBinder (fst o) t) claimText
                            (List.filter shared own))))
              where
                ownAuto : (String, String) -> Maybe (String, (String, String))
                ownAuto g = map (fst g,) (Binders.autoBinder (snd g))

                -- one the clause has as written, or under its name, a
                -- variable it binds, unless it mentions a renamed variable
                shared : (String, (String, String)) -> Bool
                shared o = (snd o `elem` around)
                  || (contains (fst (snd o)) bound && not (any (`elem` renamed) (words (fst o))))

                -- one the clause has the type of under another name
                clashing : (String, (String, String)) -> Bool
                clashing o = not (shared o) && any (\a => snd a == snd (snd o)) around

            -- lines replaced from an index on, if it is one
            splice : Maybe Int -> (count : Int) -> List String -> List String -> List String
            splice Nothing _ _ xs = xs
            splice (Just i) n new xs = List.take (cast i) xs ++ new ++ List.drop (cast (i + n)) xs

        ||| The names a helper leaves free: those of its claim's type and of its
        ||| clauses, its own names aside.
        helperFree : Subject -> (claim : Rules.Declared) -> SortedSet String
        helperFree s claim =
          let defs = Extent.definitionsOf s claim
              ofClaim = case claim.decl.val of
                PClaim c => Free.free c.type.val.type
                _ => singleton Free.unknown
              ofDefs = foldr (\d, rest => union (Free.inDecl d.decl) rest) empty defs
          in difference (union ofClaim ofDefs) (fromList claim.defines)

        ||| The names a helper's clauses refer to that its type does not: those a
        ||| value bound where it goes would capture with no type to notice.
        bodyFree : Subject -> (claim : Rules.Declared) -> SortedSet String
        bodyFree s claim =
          let ofClaim = case claim.decl.val of
                PClaim c => Free.typeNames c.type.val.type
                _ => empty
              ofDefs = foldr (\d, rest => union (Free.inDecl d.decl) rest) empty (Extent.definitionsOf s claim)
          in difference ofDefs (union ofClaim (fromList claim.defines))

        -- no name the helper's clauses refer to beyond its type's bound as a
        -- value where it goes, and its own names bound there by nothing
        noCapture : (values, types : SortedSet String) -> Either String ()
        noCapture values types =
          if contains Free.unknown (helperFree s h)
            then Left "it holds a declaration the analysis does not follow" else
            case filter (\n => Free.isVariable n && contains n values) (Prelude.toList (bodyFree s h))
                 ++ filter (\n => contains n values || contains n types) h.defines of
              [] => Right ()
              captured =>
                Left
                  ("it would be captured in `" ++ Refactoring.labelOf u ++ "` by "
                   ++ fastConcat (intersperse ", " (map (\n => "`" ++ n ++ "`") captured)))

        -- the left-hand side's variables, its head, the function or method it
        -- defines, aside
        boundOf : PClause -> SortedSet String
        boundOf cl =
          difference (Free.boundBy (Rules.lhsOf cl))
            (maybe empty (\n => singleton (nameRoot n)) (Rules.clauseName (Rules.lhsOf cl)))

        whereNames : PClause -> SortedSet String
        whereNames (MkPatClause _ _ _ wh) = fromList (foldr (\d, rest => Rules.definesOf d ++ rest) [] wh)
        whereNames _ = empty

        ||| The clauses of a declaration that a helper could move into: a
        ||| function's, or those of an implementation's methods; and the names the
        ||| declaration binds around them, its type's or its parameters'.
        clausesOf : Subject -> Rules.Declared -> Either String (List PClause, SortedSet String)
        clausesOf s u = case u.decl.val of
          PDef cls => Right (cls, ofClaim)
          PImplementation _ _ _ _ cs _ ps _ _ (Just body) =>
            Right (foldr (\d, rest => methodClauses d ++ rest) [] body,
                   foldr (\t, rest => union (Free.free t) rest)
                     (foldr (\c, rest => union (Free.free (snd c)) rest) empty cs) ps)
          PClaim _ => Left "its user uses it in a type"
          _ => Left "its user is not a function or an implementation"
          where
            methodClauses : PDecl -> List PClause
            methodClauses d = case d.val of
              PDef cls => cls
              _ => []

            -- the names the user's claim binds or leaves free: in its clauses the
            -- implicit ones are bound
            ofClaim : SortedSet String
            ofClaim = foldr (\d, rest => case d.decl.val of
                                           PClaim c => if any (`elem` u.defines) d.defines
                                             then union
                                               (Free.typeVariables (globalsOf s) c.type.val.type) rest
                                                 else rest
                                           _ => rest) empty s.declared

    candidates : Subject -> List Refactoring.Candidate
    candidates s =
      let pairs = fst (Rules.helpers s.declared)
          users = foldr (\p, rest => (snd p).defines ++ rest) [] pairs
          ready = filter (\p => not (any (`elem` users) (fst p).defines)) pairs
      in map (\p => offer (Refactoring.labelOf (fst p)) (plan s (fst p) (snd p))) ready
      where
        offer : String -> Either String (Change, Maybe Change) -> Refactoring.Candidate
        offer l (Left why) = Refactoring.candidate l (Left why)
        offer l (Right (safe, preferred)) = Refactoring.MkCandidate l (Right safe) preferred
