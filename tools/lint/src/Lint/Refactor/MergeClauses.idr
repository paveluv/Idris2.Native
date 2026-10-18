||| The refactoring `merge-clauses` (`mergeClauses`): a function several of
||| whose clauses use a helper only it uses, written as one clause, a `case`
||| of what its clauses match, so that the helper can move into the one
||| clause's `where` block (`scope-helpers`).
|||
|||     f : Maybe A -> B -> C          f : Maybe A -> B -> C
|||     f (Just x) b = e1        ==>   f y b = case y of
|||     f Nothing b = e2                 Just x => e1
|||                                      Nothing => e2
|||
||| An argument every clause names alike, or leaves `_`, stays an argument;
||| the others are the scrutinee, a tuple of them if there are several, each
||| named after its binder in the function's type, or after its type
||| (`reason` for a `NotFlatReason`), with a name the function does not use
||| and that is no keyword or common function of the Prelude.
||| The clauses' `where` blocks join the one clause's when they use nothing
||| their own patterns bind and define names apart. Each alternative keeps
||| its clause's lines, two columns in, so the layout within it stays. A
||| match a clause makes on several arguments whose types depend on each
||| other may not check as a case on a tuple: the run's check decides, as
||| only the type checker can.
module Lint.Refactor.MergeClauses

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Extent
import Lint.Refactor.Free
import Lint.Refactor.Refactoring
import Lint.Refactor.Reindent
import Lint.Refactor.Span
import Lint.Refactor.Subject

import Core.FC
import Core.Name
import Core.TT
import Core.TT.Binder
import Core.WithData
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedSet
import Data.String
import Data.Zippable
import Idris.Syntax
import Libraries.Data.WithData
import Lint.Rules
import Lint.Source

%default covering

||| An argument of a clause's left-hand side: an explicit one, its pattern;
||| or another, as written (`{n = k}`, `@{d}`), which every clause must
||| write alike.
data Arg = Explicit PTerm | Written String

||| A clause taken apart: its head as written and its arguments; its first
||| line, the column it starts at, and the column its left-hand side ends
||| at; the last line of its body, before its `where` block, and its last
||| line; and its `where` block: its declarations, its lines, and the
||| column they start at.
record Parts where
  constructor MkParts
  head : String
  args : List Arg
  first : Int
  column : Int
  lhsEnd : Int
  bodyLast : Int
  last : Int
  wheres : List PDecl
  whereText : List String
  whereColumn : Int
  clause : PClause

||| What becomes of an argument: one every clause names alike, or leaves
||| `_`, kept under that name; one the case matches; one written alike by
||| every clause, kept as written.
data Position = Kept String | Matched | Fixed String

||| `merge-clauses`: each function several clauses of which use a helper
||| only it uses, written as one clause with a `case`.
export
mergeClauses : Refactoring
mergeClauses = fileRefactoring "merge-clauses"
  "write as one clause with a `case` each function several clauses of which use a helper only it uses"
  candidates
  where
    ||| A line of the text, or an empty one past its end.
    lineAt : List String -> Int -> String
    lineAt ls l = fromMaybe "" (head' (drop (cast l) ls))

    ||| The text of a source location on one line.
    textAt : List String -> FC -> Either String String
    textAt ls fc = case bounds fc of
      Just ((l, a), (l', b)) =>
        if l == l' then Right (substr (cast a) (cast (b - a)) (lineAt ls l)) else Left ("a pattern at line " ++ show (l + 1) ++ " spans lines")
      Nothing => Left "a pattern has no place in the source"

    ||| The lines from `a` to `b`, both included.
    linesFrom : List String -> (a, b : Int) -> List String
    linesFrom ls a b = take (cast (b - a + 1)) (drop (cast a) ls)

    ||| A clause taken apart, or why it cannot be: a `with` clause, an
    ||| impossible one, a left-hand side over several lines, or a `where`
    ||| written after code on its line.
    partsOf : List String -> PClause -> Either String Parts
    partsOf _ (MkWithClause fc _ _ _ _) = Left ("its clause at line " ++ show (fst (lineSpan fc) + 1) ++ " is a `with` clause")
    partsOf _ (MkImpossible fc _) = Left ("its clause at line " ++ show (fst (lineSpan fc) + 1) ++ " is impossible")
    partsOf ls cl@(MkPatClause fc lhs _ wh) = do
      ((l0, c0), _) <- maybe (Left "a clause has no place in the source") Right (bounds fc)
      ((ll, _), (le, lce)) <- maybe (Left "a left-hand side has no place in the source") Right (bounds (getPTermLoc lhs))
      when (ll /= le) $ Left ("the left-hand side at line " ++ show (ll + 1) ++ " spans lines")
      (h, args) <- spine ls lhs
      let last = foldr (\d, m => max m (snd (lineSpan d.fc))) (snd (lineSpan fc)) wh
      (bodyLast, wtext, wcol) <- whereOf l0 last
      pure (MkParts h (args <>> []) l0 c0 lce bodyLast last wh wtext wcol cl)
      where
        ||| The last line from `l` down to `lo` with something on it, or `lo`.
        lastWritten : List String -> (lo, l : Int) -> Int
        lastWritten ls lo l = if l <= lo || trim (lineAt ls l) /= "" then max lo l else lastWritten ls lo (l - 1)

        -- the last line of the body; the `where` block's lines, from the
        -- comments above its first declaration; and its column
        whereOf : (first, last : Int) -> Either String (Int, List String, Int)
        whereOf first last = case sort (map (fst . lineSpan . (.fc)) wh) of
          [] => Right (lastWritten ls first last, [], 0)
          (top :: _) =>
            let from = attachedFrom ls top
                kw = lastWritten ls first (from - 1)
            in if trim (lineAt ls kw) /= "where"
                 then Left ("the `where` of its clause at line " ++ show (first + 1) ++ " is written after code on its line")
                 else Right (lastWritten ls first (kw - 1), linesFrom ls from last, foldr (\d, m => min m (startColumn d.fc)) 1000 wh)

        ||| A clause's left-hand side as its head and its arguments, in order.
        spine : List String -> PTerm -> Either String (String, SnocList Arg)
        spine ls (PRef fc _) = map (, [<]) (textAt ls fc)
        spine ls (PApp _ f x) = map (\(h, as) => (h, as :< Explicit x)) (spine ls f)
        spine ls (PNamedApp fc f _ _) = do (h, as) <- spine ls f; t <- after (getPTermLoc f) fc; pure (h, as :< Written t)
          where
            after : FC -> FC -> Either String String
            after inner outer = case (bounds inner, bounds outer) of
              (Just (_, (l, a)), Just (_, (l', b))) => if l == l' then Right (trim (substr (cast a) (cast (b - a)) (lineAt ls l))) else Left "an implicit argument spans lines"
              _ => Left "an implicit argument has no place in the source"
        spine ls (PAutoApp fc f _) = do (h, as) <- spine ls f; t <- after (getPTermLoc f) fc; pure (h, as :< Written t)
          where
            after : FC -> FC -> Either String String
            after inner outer = case (bounds inner, bounds outer) of
              (Just (_, (l, a)), Just (_, (l', b))) => if l == l' then Right (trim (substr (cast a) (cast (b - a)) (lineAt ls l))) else Left "an auto-implicit argument spans lines"
              _ => Left "an auto-implicit argument has no place in the source"
        spine _ _ = Left "a left-hand side is not the function applied to patterns"

    ||| The kind of each argument, `Nothing` for an explicit one, the text for
    ||| another, if every clause has the same.
    sameShape : List Parts -> Either String (List (Maybe String))
    sameShape [] = Left "it has no clauses"
    sameShape (p :: ps) =
      let shape = map kind p.args in
      if all (\q => map kind q.args == shape) ps then Right shape
      else Left "its clauses differ in how many arguments they take, or in their implicit ones"
      where
        kind : Arg -> Maybe String
        kind (Explicit _) = Nothing
        kind (Written t) = Just t

    ||| The pattern a clause has at an argument, explicit, if it has one there.
    patternAt : Nat -> Parts -> Maybe PTerm
    patternAt i p = case drop i p.args of
      (Explicit t :: _) => Just t
      _ => Nothing

    ||| What becomes of each argument, given the clauses' shape.
    positions : List Parts -> List (Maybe String) -> List Position
    positions parts shape = zipWith decide [0 .. length shape] shape
      where
        ||| A pattern as a variable, if it is one.
        variableOf : PTerm -> Maybe String
        variableOf (PRef _ (UN (Basic v))) = if isVariable v then Just v else Nothing
        variableOf _ = Nothing

        plain : PTerm -> Bool
        plain (PImplicit _) = True
        plain t = isJust (variableOf t)

        decide : Nat -> Maybe String -> Position
        decide _ (Just t) = Fixed t
        decide i Nothing =
          let pats = mapMaybe (patternAt i) parts
              names = nub (mapMaybe variableOf pats)
          in if all plain pats && null (drop 1 names) then Kept (fromMaybe "_" (head' names)) else Matched

    ||| The explicit binders of a type, in order: each name, if it has one, and
    ||| its type.
    explicitBinders : PTerm -> List (Maybe String, PTerm)
    explicitBinders (NewPi b) = case b.val.binder.info of
      Explicit => map (\n => (plain n.val, b.val.binder.bind.type)) (forget b.val.binder.bind.names) ++ explicitBinders b.val.scope
      _ => explicitBinders b.val.scope
      where
        plain : Name -> Maybe String
        plain (UN (Basic s)) = Just s
        plain _ = Nothing
    explicitBinders (PPi _ _ Explicit n a r) = (map nameRoot n, a) :: explicitBinders r
    explicitBinders (PPi _ _ _ _ _ r) = explicitBinders r
    explicitBinders (Forall b) = explicitBinders (snd b.val)
    explicitBinders _ = []

    ||| The words a text could use as names.
    identifiers : String -> List String
    identifiers t = filter (/= "") (forget (split (\c => not (isAlphaNum c || c == '_' || c == '\'')) t))

    ||| The words Idris keeps for itself, which no name may be.
    keywords : List String
    keywords = ["case", "of", "do", "let", "in", "where", "if", "then", "else", "with", "data", "record", "module", "import",
                "using", "open", "parameters", "implicit", "auto", "default", "impossible", "total", "partial", "covering",
                "export", "public", "private", "namespace", "interface", "implementation", "forall", "rewrite", "mutual",
                "infix", "infixl", "infixr", "prefix", "failing", "constructor", "proof", "syntax"]

    ||| The Prelude's functions a name after a type could be (`maybe` after
    ||| `Maybe`, `all` after `All`), which a reader would take for those.
    preludeFunctions : List String
    preludeFunctions = ["maybe", "either", "id", "const", "show", "map", "pure", "fst", "snd", "not", "length", "reverse",
                        "filter", "head", "tail", "elem", "lookup", "max", "min", "pred", "succ", "negate", "abs", "cast", "the",
                        "all", "any", "and", "or", "sum", "product", "concat", "zip", "take", "drop", "lines", "words",
                        "pack", "unpack", "print", "ignore", "when", "flip", "compare", "div", "mod", "force", "delay"]

    ||| A name for each matched argument, in order: its binder's in the type,
    ||| or one after its type, that one with a prime (`body'`, when the module
    ||| has a `body`), or `x`, `y`, `z`, the first the function does not use;
    ||| failing all, one of them with primes. A word after a type that is a
    ||| keyword or a function of the Prelude is no name, primed or not.
    scrutineeNames : (avoid : SortedSet String) -> List (Maybe (Maybe String, PTerm)) -> List String
    scrutineeNames _ [] = []
    scrutineeNames avoid (b :: bs) =
      let word = ownWord (b >>= (typeWord . snd))
          tries = catMaybes [b >>= fst, word, map (++ "'") word] ++ ["x", "y", "z"]
          n = fromMaybe (primed (fromMaybe "x" (head' tries))) (find (\t => not (contains t avoid)) tries)
      in n :: scrutineeNames (insert n avoid) bs
      where
        primed : String -> String
        primed n = if contains (n ++ "'") avoid then primed (n ++ "'") else n ++ "'"

        ownWord : Maybe String -> Maybe String
        ownWord (Just w) = if (w `elem` keywords) || (w `elem` preludeFunctions) then Nothing else Just w
        ownWord Nothing = Nothing

        ||| A name for a value of a type, after the last word of its head:
        ||| `reason` for a `NotFlatReason`, `instr` for an `Instr`.
        typeWord : PTerm -> Maybe String
        typeWord t = do
          h <- headOf t
          let w = lastWord (unpack h)
          if null w then Nothing else Just (toLower (pack w))
          where
            headOf : PTerm -> Maybe String
            headOf (PRef _ n) = Just (nameRoot n)
            headOf (PApp _ f _) = headOf f
            headOf (PNamedApp _ f _ _) = headOf f
            headOf (PBracketed _ x) = headOf x
            headOf _ = Nothing

            lastWord : List Char -> List Char
            lastWord cs = let (low, rest) = span (not . isUpper) (reverse cs) in reverse (low ++ take 1 rest)

    ||| A pattern as an alternative writes it: as written, or without the
    ||| parentheses around an application.
    patternText : List String -> PTerm -> Either String String
    patternText ls (PBracketed fc t) = if bare t then textAt ls (getPTermLoc t) else textAt ls fc
      where
        bare : PTerm -> Bool
        bare (PApp _ _ _) = True
        bare (PNamedApp _ _ _ _) = True
        bare (PAutoApp _ _ _) = True
        bare (POp _ _ _ _) = True
        bare _ = False
    patternText ls t = textAt ls (getPTermLoc t)

    ||| Spaces, `n` of them.
    indent : Int -> String
    indent n = pack (List.replicate (cast n) ' ')

    ||| A line two columns further in, a blank one left blank.
    shift : String -> String
    shift l = if trim l == "" then "" else "  " ++ l

    ||| A clause as an alternative of the case: its pattern then `=>` where its
    ||| `=` was, its lines two columns further in. When the right-hand side
    ||| opens a layout block on the clause's first line and lines below line
    ||| up with it, the arrow takes the `=`'s place, so that what follows it
    ||| moves only the two columns the rest does.
    alternative : List String -> (column : Int) -> (pattern : String) -> Parts -> Either String (List String)
    alternative ls c pat p =
      let line0 = lineAt ls p.first
          rest0 = substr (cast p.lhsEnd) (length line0) line0
          t = ltrim rest0
          more = linesFrom ls (p.first + 1) p.bodyLast
          lead = indent (c + 2) ++ pat
      in if isPrefixOf "=" t && not (isPrefixOf "==" t) then sameLine (p.lhsEnd + cast (length rest0) - cast (length t)) line0 more lead
         else if t == "" then nextLine more lead
         else Left ("its clause at line " ++ show (p.first + 1) ++ " has more than `=` after its left-hand side")
      where
        ||| Whether a line's text opens a layout block with something after it on
        ||| the line, which the lines below may line up with.
        opensLayout : String -> Bool
        opensLayout t = go (words t)
          where
            go : List String -> Bool
            go (w :: rest@(_ :: _)) = (w `elem` the (List String) ["do", "let", "of", "where"]) || go rest
            go _ = False

        sameLine : (eq : Int) -> String -> List String -> String -> Either String (List String)
        sameLine eq line0 more lead =
          let afterEq = substr (cast (eq + 1)) (length line0) line0
              width = cast {to = Int} (length lead)
          in if not (null more) && opensLayout afterEq
               then (if width + 1 > eq + 1 then Left ("its clause at line " ++ show (p.first + 1) ++ " leaves no room for its arrow")
                     else Right ((lead ++ indent (eq + 1 - width) ++ "=>" ++ afterEq) :: map shift more))
               else Right ((lead ++ " =>" ++ afterEq) :: map shift more)

        nextLine : List String -> String -> Either String (List String)
        nextLine more lead =
          let (before, from) = break (\l => isPrefixOf "=" (ltrim l)) more in
          case from of
            [] => Left ("its clause at line " ++ show (p.first + 1) ++ " has no `=`")
            (eqLine :: rest) =>
              let sp = cast {to = Int} (length eqLine) - cast (length (ltrim eqLine)) in
              if not (all (\l => trim l == "" || isPrefixOf "--" (trim l)) before) || sp < c + 2
                then Left ("the `=` of its clause at line " ++ show (p.first + 1) ++ " has no room for an arrow")
                else Right (lead :: map shift before ++ [indent (sp + 1) ++ "=>" ++ substr (cast (sp + 1)) (length eqLine) eqLine] ++ map shift rest)

    ||| The function's lines rewritten, or why they stay.
    plan : Subject -> (user : Declared) -> List PClause -> (type : Maybe PTerm) -> Either String Change
    plan s u cls ty = do
      parts <- traverse (partsOf ls) cls
      shape <- sameShape parts
      c <- oneColumn parts
      let ps = positions parts shape
          region = (maybe 0 (.first) (head' parts), foldr (\p, m => max m p.last) 0 parts)
          names = scrutineeNames (avoid region) (matchedBinders ps)
      when (not (any isMatched ps)) $ Left "its clauses match on no argument"
      inOrder parts
      nothingBetween region
      keptUncaptured ps parts
      wheresJoin ps parts
      alts <- traverse (\p => do pat <- alternativePattern ps p; alternative ls c pat p) parts
      let header = indent c ++ maybe "" (.head) (head' parts) ++ fastConcat (map (" " ++) (argTexts ps names)) ++ " = case " ++ scrutinee names ++ " of"
      pure (inFile s.file.path [replaceLines (fst region) (snd region) (header :: joinAlts parts alts ++ whereBlock c parts)])
      where
        ls : List String
        ls = linesOf s

        isMatched : Position -> Bool
        isMatched Matched = True
        isMatched _ = False

        oneColumn : List Parts -> Either String Int
        oneColumn [] = Left "it has no clauses"
        oneColumn (p :: more) = if all (\q => q.column == p.column) more then Right p.column else Left "its clauses start at different columns"

        inOrder : List Parts -> Either String ()
        inOrder (p :: rest@(q :: _)) = if p.last < q.first then inOrder rest else Left "its clauses are not written one after another"
        inOrder _ = Right ()

        -- no other declaration of the module among the clauses
        nothingBetween : (Int, Int) -> Either String ()
        nothingBetween (a, b) =
          if any (\d => let l = fst (lineSpan d.decl.fc) in l >= a && l <= b && lineSpan d.decl.fc /= lineSpan u.decl.fc) s.declared
            then Left "other declarations lie between its clauses" else Right ()

        -- the names the scrutinee may not take: those written in the
        -- clauses, those the type has in scope in them, the module's, and
        -- Idris's own words
        avoid : (Int, Int) -> SortedSet String
        avoid (a, b) =
          let written = identifiers (joinBy "\n" (linesFrom ls a b))
              inType = maybe [] (\t => Prelude.toList (typeNames t)) ty
              explicit = maybe [] (\t => mapMaybe fst (explicitBinders t)) ty
              globals = foldr (\d, rest => d.defines ++ rest) [] s.declared
          in fromList (written ++ filter (\n => not (n `elem` explicit)) inType ++ globals ++ keywords ++ preludeFunctions)

        -- the explicit binder of the type at each matched argument
        matchedBinders : List Position -> List (Maybe (Maybe String, PTerm))
        matchedBinders ps =
          let binders = maybe [] explicitBinders ty
              explicitAt = explicitIndices 0 ps
          in mapMaybe (\(k, pos) => case pos of
                                      Matched => Just (head' (drop k binders))
                                      _ => Nothing) explicitAt
          where
            -- each argument with its place among the explicit ones
            explicitIndices : Nat -> List Position -> List (Nat, Position)
            explicitIndices _ [] = []
            explicitIndices k (Fixed t :: more) = (k, Fixed t) :: explicitIndices k more
            explicitIndices k (pos :: more) = (k, pos) :: explicitIndices (S k) more

        argTexts : List Position -> List String -> List String
        argTexts [] _ = []
        argTexts (Kept n :: more) ns = n :: argTexts more ns
        argTexts (Fixed t :: more) ns = t :: argTexts more ns
        argTexts (Matched :: more) (n :: ns) = n :: argTexts more ns
        argTexts (Matched :: more) [] = argTexts more []

        scrutinee : List String -> String
        scrutinee [n] = n
        scrutinee ns = "(" ++ joinBy ", " ns ++ ")"

        -- the patterns a clause matches the scrutinee with
        alternativePattern : List Position -> Parts -> Either String String
        alternativePattern ps p = do
          pats <- traverse (patternText ls) (mapMaybe (\(i, pos) => case pos of
                                                                      Matched => patternAt i p
                                                                      _ => Nothing) (zip [0 .. length ps] ps))
          pure (scrutinee pats)

        -- the variables a clause's matched patterns bind
        patternVariables : List Position -> Parts -> SortedSet String
        patternVariables ps p =
          foldr (\(i, pos), rest => case pos of
                                      Matched => maybe rest (\t => union (boundBy t) rest) (patternAt i p)
                                      _ => rest) empty (zip [0 .. length ps] ps)

        -- a name kept as an argument binds, in a clause that left it `_`,
        -- nothing the clause refers to
        keptUncaptured : List Position -> List Parts -> Either String ()
        keptUncaptured ps parts =
          case filter captured (zip [0 .. length ps] ps) of
            [] => Right ()
            ((_, Kept n) :: _) => Left ("the argument `" ++ n ++ "` would capture what a clause leaving it `_` refers to")
            _ => Right ()
          where
            captured : (Nat, Position) -> Bool
            captured (i, Kept n) = n /= "_" && any (\p => maybe False isWild (patternAt i p) && contains n (inClause p.clause)) parts
              where
                isWild : PTerm -> Bool
                isWild (PImplicit _) = True
                isWild _ = False
            captured _ = False

        -- the clauses' `where` blocks, joined, mean what they did: none
        -- uses by name what its clause's patterns bind, none defines a name
        -- another defines or another clause refers to. What one finds by
        -- search, an implicit a pattern binds such as `{fx}`, no name
        -- shows: the type checker judges that
        wheresJoin : List Position -> List Parts -> Either String ()
        wheresJoin ps parts = traverse_ one parts
          where
            one : Parts -> Either String ()
            one p =
              let defs = fromList (definedBy p.wheres)
                  used = difference (foldr (\d, rest => union (inDecl d) rest) empty p.wheres) defs
                  others = filter (\q => q.first /= p.first) parts
              in if contains unknown used then Left ("the `where` block of its clause at line " ++ show (p.first + 1) ++ " holds a declaration the analysis does not follow")
                 else if not (null (intersection used (patternVariables ps p))) then Left ("the `where` block of its clause at line " ++ show (p.first + 1) ++ " uses what the clause's patterns bind")
                 else if any (\q => not (null (intersection defs (union (fromList (definedBy q.wheres)) (inClause q.clause))))) others
                   then Left ("the `where` block of its clause at line " ++ show (p.first + 1) ++ " defines a name another clause has")
                 else Right ()

        joinAlts : List Parts -> List (List String) -> List String
        joinAlts (p :: rest@(q :: _)) (a :: as) = a ++ map shift (linesFrom ls (p.last + 1) (q.first - 1)) ++ joinAlts rest as
        joinAlts _ (a :: _) = a
        joinAlts _ [] = []

        whereBlock : Int -> List Parts -> List String
        whereBlock c parts = case filter (\p => not (null p.whereText)) parts of
          [] => []
          ws => (indent (c + 2) ++ "where") :: intercalate [""] (map (\p => reindent p.whereColumn (c + 4) p.whereText) ws)

    claimType : Subject -> Declared -> Maybe PTerm
    claimType s u = do
      c <- find (\d => isClaim d && any (`elem` u.defines) d.defines) s.declared
      case c.decl.val of
        PClaim cd => Just cd.type.val.type
        _ => Nothing
      where
        isClaim : Declared -> Bool
        isClaim d = case d.decl.val of
          PClaim _ => True
          _ => False

    -- the functions a helper's one user has that several clauses of use it:
    -- the user, or methods of it if it is an implementation
    targetsOf : Subject -> (Declared, Declared) -> List Candidate
    targetsOf s (h, u) = case u.decl.val of
      PDef cls => if usedBy cls >= 2 then [candidate (labelOf u) (plan s u cls (claimType s u))] else []
      PImplementation _ _ _ _ _ _ _ _ _ (Just body) =>
        mapMaybe (\d => case d.val of
                          PDef cls => if usedBy cls >= 2 then Just (candidate (fastConcat (definesOf d) ++ " of " ++ labelOf u) (plan s u cls Nothing)) else Nothing
                          _ => Nothing) (foldr (\d, rest => byFunction d ++ rest) [] body)
      _ => []
      where
        usedBy : List PClause -> Nat
        usedBy cls = length (filter (\cl => any (\n => contains n (inClause cl)) h.defines) cls)

    candidates : Subject -> List Candidate
    candidates s = nubBy (\a, b => a.label == b.label) (foldr (\p, rest => targetsOf s p ++ rest) [] (fst (helpers s.declared)))
