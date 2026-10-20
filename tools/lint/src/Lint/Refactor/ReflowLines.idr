||| The refactoring `reflow-lines` (`reflowLines`): each line longer than a
||| width broken into lines that fit, its layout kept.
|||
||| A line breaks where it has spaces between two tokens, outside its strings
||| and its comment, at the fewest brackets it can and the last place there
||| the text before fits: between statements (`a; b`) first, which makes the
||| next a statement of its own at its block's column; else after `,`; else
||| after `=`, `=>` or `->`, or before an operator, `then` or `else`; else one
||| bracket in, between statements or after a comma, if the place here would
||| leave a name alone (`pure`); else anywhere. What follows goes on a line of
||| its own, indented past the line's start and every layout block open there:
||| a signature's type after its `: `, a bracket's contents after the bracket
||| where they fit there, an operator two columns past the line's start, the
||| rest two past the piece's. A line breaks nowhere that would move the start
||| of a block the next lines align with (`p` in `Just f => do p <- emit x`),
||| nor in a named argument's braces. The pieces break again until they fit or
||| nowhere is left, and a block whose statements come to span pieces has each
||| on a line of its own. A line wider only for the comment after its code
||| keeps its code whole, and the comment goes on a line of its own above
||| it, at its indentation. A comment line is left as it is. Layout is all
||| the text tells; the type checker judges the rest.
module Lint.Refactor.ReflowLines

import Lint.Refactor.Change
import Lint.Refactor.Edit
import Lint.Refactor.Refactoring
import Lint.Refactor.Subject

import Data.List
import Data.String
import Data.Zippable
import Lint.Source

%default covering

||| A layout block open in a line: the column of its first token, the
||| brackets open around it, the piece of the line it opens in, and the
||| keyword that opens it (`do`, `of`, `let`, `where`, or the line itself).
record Block where
  constructor MkBlock
  column : Int
  depth : Nat
  piece : Nat
  keyword : String

||| Where a line may break: the spaces from `from` to `to`, the brackets
||| open there with the innermost and its column, the blocks open there,
||| innermost first, and the tokens on either side.
record Gap where
  constructor MkGap
  from : Int
  to : Int
  depth : Nat
  bracket : Maybe (Int, String)
  blocks : List Block
  before : String
  after : String

||| What a line's pieces read so far leave open, and the gaps of the piece
||| that breaks.
record Lexed where
  constructor MkLexed
  brackets : List (Int, String)
  blocks : List Block
  ||| A keyword whose block starts at the next token.
  pending : Maybe String
  previous : String
  ||| The spaces before the next token, if any.
  spaces : Maybe (Int, Int)
  gaps : List Gap

||| How a piece breaks: where, the next piece's indentation, and whether
||| the `;` before the break goes.
record Break where
  constructor MkBreak
  gap : Gap
  indent : Int
  statement : Bool

||| A line's code and the comment after it, `-- ...`, if it has one: outside
||| its strings and character literals, a `--` that no operator's characters
||| follow. The code without the spaces before the comment.
export
trailingComment : String -> Maybe (String, String)
trailingComment l = go [] (unpack l)
  where
    opChar : Char -> Bool
    opChar c = c `elem` unpack ":!#$%&*+./<=>?@\\^|-~"

    -- the rest of a string literal, its closing quote included
    string : List Char -> List Char -> (List Char, List Char)
    string acc ('\\' :: x :: rest) = string (x :: '\\' :: acc) rest
    string acc ('"' :: rest) = ('"' :: acc, rest)
    string acc (x :: rest) = string (x :: acc) rest
    string acc [] = (acc, [])

    go : List Char -> List Char -> Maybe (String, String)
    go _ [] = Nothing
    go acc ('-' :: '-' :: rest) =
      if maybe True (not . opChar) (head' rest) && not (null acc)
         then Just (pack (reverse (dropWhile (== ' ') acc)), "--" ++ pack rest)
         else go ('-' :: '-' :: acc) rest
    go acc ('"' :: rest) = let (s, rest') = string ('"' :: acc) rest in go s rest'
    go acc ('\'' :: x :: '\'' :: rest) = go ('\'' :: x :: '\'' :: acc) rest
    go acc (x :: rest) = go (x :: acc) rest

||| The width a line has, in characters.
width : String -> Int
width l = cast (length l)

||| A line broken into pieces each no wider than the limit, as far as it
||| can be; nothing if it cannot be broken at all.
export
reflow : (limit : Int) -> String -> Maybe (List String)
reflow limit l = let ps =
                       go (the Nat 50) 0 (everyStatement (the Nat 50) 0 (go (the Nat 50) 0 [l])) in
                  if length ps > 1 then Just ps else Nothing
  where
    split : Nat -> Break -> List String -> List String
    split i b ps = case splitAt i ps of
      (before, p :: after) =>
        let cut = if b.statement then b.gap.from - 1 else b.gap.from
            first = rtrim (substr 0 (cast cut) p)
            rest = pack (replicate (cast b.indent) ' ') ++ substr (cast b.gap.to) (length p) p
        in before ++ first :: rest :: after
      _ => ps

    ||| How the piece at `target` breaks best, if anywhere; if `statements`,
    ||| only between statements of a block an earlier piece opens, at the
    ||| first place.
    chooseBreak : (limit : Int) -> (statements : Bool) -> (pieces : List String) ->
                  (target : Nat) -> Maybe Break
    chooseBreak limit statements ps target =
      let st = lexPieces target ps
          ownIndent = maybe 0 indentOf (head' (drop target ps))
          firstIndent = maybe 0 indentOf (head' ps)
          signature = head' ps >>= signatureColumn
          -- the blocks this piece starts that the pieces or lines after it
          -- align with: nothing at or before their first tokens moves
          held =
            foldl (\m, b => if b.piece == target && b.keyword /= "line" then max m b.column else m)
              (-1) st.blocks
          ownWidth = maybe 0 width (head' (drop target ps))
          breaks =
            filter (\b => b.statement || not statements)
              (mapMaybe (breakAt firstIndent ownIndent ownWidth signature held) (reverse st.gaps))
      in case breaks of
           [] => Nothing
           _ => if statements
             then find
               (\b => b.statement && maybe False (\k => k.piece < target) (head' b.gap.blocks))
                 breaks else
             let d =
                   foldl (\m, b => min m b.gap.depth) (foldl (\m, b => max m b.gap.depth) 0 breaks)
                     breaks
                 fits = \b => b.gap.from <= limit
                 statementsAt = \k =>
                   filter (\b => b.statement && fits b && b.gap.depth == k) breaks
                 atDepth = filter (\b => b.gap.depth == d) breaks
                 fitting = filter fits atDepth
                 -- a comma first: it parts what a bracket holds, operators
                 -- only within a part
                 good = case filter (\b => b.gap.before == ",") fitting of
                          [] => filter (\b => goodAt b.gap) fitting
                          cs => cs
                 -- one bracket in, a statement or a comma is better than a
                 -- plain place here that leaves a name alone: `emit (case o of
                 -- A => a` before `B => b)`, `pure (a,` before `b)`, not `emit`
                 -- or `pure` before the rest
                 inner = statementsAt (S d)
                   ++ filter (\b => b.gap.depth == S d && fits b && b.gap.before == ",") breaks
                 -- a plain place that leaves a function's name alone
                 headOnly = map (.gap.from) (last' fitting) == map (.gap.from) (head' atDepth)
             in case (statementsAt d, good, inner, fitting) of
                  (s :: _, _, _, _) => Just s
                  (_, g@(_ :: _), _, _) => last' g
                  (_, _, n :: _, f) => if headOnly || null f then Just n else last' f
                  (_, _, _, f@(_ :: _)) => last' f
                  _ => head' atDepth
      where
        operator : String -> Bool
        operator t =
          t `elem` ["++",
            "::", "&&", "||", ">>=", "<|>", "<+>", "|", "$", "+", "-", "*", "==", "/=", "<", "<=",
                    ">", ">="]

        goodAt : Gap -> Bool
        goodAt g = (g.before `elem` ["=", "=>", "->", ",", "$"]) || operator g.after
          || (g.after `elem` ["then", "else"])

        ||| Whether a token opens a bracket.
        opening : String -> Bool
        opening t = t == "(" || t == "[" || t == "{"

        ||| Whether a token closes a bracket.
        closing : String -> Bool
        closing t = t == ")" || t == "]" || t == "}"

        -- a break at a gap, where the piece starts at `ownIndent` and is
        -- `ownWidth` wide, and nothing at or before `held` moves; none within
        -- a named argument's or a record's braces
        breakAt : (firstIndent, ownIndent, ownWidth : Int) -> (signature : Maybe Int) ->
                  (held : Int) -> Gap -> Maybe Break
        breakAt firstIndent ownIndent ownWidth signature held g =
          if g.to <= held || opening g.before || closing g.after || (g.before `elem` ["\\", ""])
            || map snd g.bracket == Just "{"
               || (g.after `elem` ["=", "=>", "->", "<-", ":", ",", "of", ";"])
            then Nothing
          else if g.before == ";" then
            case g.blocks of
              (b :: _) => if b.depth == g.depth && b.column < g.to
                then Just (MkBreak g b.column True) else Nothing
              [] => Nothing
          else
            let lower = max (firstIndent + 1) (foldl (\m, b => max m (b.column + 2)) 0 g.blocks)
                -- inside a bracket, past it, unless what follows would not
                -- fit there
                preferred = case (g.bracket, signature) of
                              (Just (c, _), _) => if c + 1 + ownWidth - g.to <= limit then c + 1
                                else ownIndent + 2
                              (Nothing, Just s) => s
                              -- an operator at the top applies to all before it
                              (Nothing, Nothing) => if operator g.after then firstIndent + 2
                                else ownIndent + 2
                indent = max preferred lower
            in if indent < g.to then Just (MkBreak g indent False) else Nothing

        ||| The column a line's text starts at.
        indentOf : String -> Int
        indentOf l = cast (length (takeWhile (== ' ') (unpack l)))

        ||| The column after a signature's `: `, if the line declares names
        ||| (`f : ...`, `a, b : ...`).
        signatureColumn : String -> Maybe Int
        signatureColumn l = names (indentOf l) (drop (cast (indentOf l)) (unpack l))
          where
            isNameChar : Char -> Bool
            isNameChar c = isAlphaNum c || c == '_' || c == '\''

            names : Int -> List Char -> Maybe Int
            names c cs = case span isNameChar cs of
              ([], _) => Nothing
              (n, ',' :: ' ' :: rest) => names (c + cast (length n) + 2) rest
              (n, ' ' :: ':' :: ' ' :: _) => Just (c + cast (length n) + 3)
              _ => Nothing

        ||| The pieces of a line read up to the one that breaks, each from where the
        ||| last left off: the brackets and blocks open at its end, and its gaps.
        lexPieces : (target : Nat) -> List String -> Lexed
        lexPieces target ps =
          foldl (\st, (i, p) => lexPiece i st (unpack p)) start
            (zip [0 .. target] (take (S target) ps))
          where
            start : Lexed
            start =
              MkLexed [] [MkBlock (maybe 0 indentOf (head' ps)) 0 0 "line"] Nothing "" Nothing []

            isOpChar : Char -> Bool
            isOpChar c = c `elem` unpack ":!#$%&*+./<=>?@\\^|-~"

            isNameChar : Char -> Bool
            isNameChar c = isAlphaNum c || c == '_' || c == '\''

            -- a token's text and what follows it
            token : Char -> List Char -> (String, List Char)
            token '"' cs = let (s, rest) = inString cs in (pack ('"' :: s), rest)
              where
                inString : List Char -> (List Char, List Char)
                inString ('\\' :: x :: more) = let (s, rest) =
                                                     inString more in ('\\' :: x :: s, rest)
                inString ('"' :: more) = (['"'], more)
                inString (x :: more) = let (s, rest) = inString more in (x :: s, rest)
                inString [] = ([], [])
            token '`' cs = let (n, rest) = span (/= '`') cs in (pack ('`' :: n) ++ "`", drop 1 rest)
            token c cs =
              if isAlphaNum c || c == '_' then let (n, rest) = qualified cs in (pack (c :: n), rest)
              else if isOpChar c then let (o, rest) = span isOpChar cs in (pack (c :: o), rest)
              else (pack [c], cs)
              where
                -- a name and the dotted parts after it (`TermIR.Opnd.V`, `x.field`)
                qualified : List Char -> (List Char, List Char)
                qualified ('.' :: x :: more) =
                  if isAlphaNum x || x == '_' then let (n, rest) =
                                                         qualified more in ('.' :: x :: n, rest)
                                                           else ([], '.' :: x :: more)
                qualified (x :: more) = if isNameChar x then let (n, rest) =
                                                                   qualified more in (x :: n, rest)
                                                                     else ([], x :: more)
                qualified [] = ([], [])

            -- a token read at a column: the gap before it noted, the brackets and
            -- blocks it opens or closes
            read : Nat -> Lexed -> Int -> String -> Lexed
            read i st c t =
              let depth = length st.brackets
                  gaps = case st.spaces of
                           Just (a, b) => if i == target
                             then MkGap a b depth (head' st.brackets) st.blocks st.previous t
                             :: st.gaps else st.gaps
                           Nothing => st.gaps
                  opened = case st.pending of
                             Just k => if closing t then st.blocks else MkBlock c depth i k
                               :: st.blocks
                             Nothing => st.blocks
                  st' = { gaps := gaps, spaces := Nothing, previous := t, blocks := opened,
                          pending := if (t `elem` ["do", "of", "let", "where"])
                            || (t == "case" && st.previous == "\\") then Just t else Nothing } st
              in if opening t then { brackets $= ((c, t) ::) } st'
                 else if closing t then
                   let rest =
                         drop 1 st'.brackets in
                           { brackets := rest, blocks $= filter (\b => b.depth <= length rest) } st'
                 else if t == "in" then { blocks $= dropLet } st'
                 else st'
              where
                dropLet : List Block -> List Block
                dropLet (b :: bs) = if b.keyword == "let" then bs else b :: bs
                dropLet [] = []

            lexPiece : Nat -> Lexed -> List Char -> Lexed
            lexPiece i st cs = go st 0 cs
              where
                go : Lexed -> Int -> List Char -> Lexed
                go st _ [] = { spaces := Nothing } st
                go st c (' ' :: more) =
                  let (sp, rest) = span (== ' ') more
                      c' = c + 1 + cast (length sp)
                  in go (if c == 0 then st else { spaces := Just (c, c') } st) c' rest
                go st c ('-' :: '-' :: more) = if maybe True (not . isOpChar) (head' more)
                  then { spaces := Nothing } st else
                  let (t, rest) = token '-' ('-' :: more) in go (read i st c t) (c + width t) rest
                go st c ('{' :: '-' :: _) = { spaces := Nothing } st
                go st c ('\'' :: more) = let (lit, rest) =
                                               charLiteral more in go (read i st c lit)
                                                 (c + width lit) rest
                  where
                    charLiteral : List Char -> (String, List Char)
                    charLiteral ('\\' :: x :: '\'' :: rest) = (pack ['\'', '\\', x, '\''], rest)
                    charLiteral (x :: '\'' :: rest) = (pack ['\'', x, '\''], rest)
                    charLiteral rest = ("'", rest)
                go st c (x :: more) = let (t, rest) =
                                            token x more in go (read i st c t) (c + width t) rest

    -- the pieces after a break between statements, each the next
    -- statement, up to the block's last
    statementsFrom : Nat -> Nat -> List String -> List String
    statementsFrom Z _ ps = ps
    statementsFrom (S fuel) i ps = case chooseBreak limit True ps i of
      Just b => statementsFrom fuel (S i) (split i b ps)
      Nothing => ps

    -- the pieces from the `i`th on broken between each two statements of
    -- a block that spans pieces, so that each is on a line of its own
    everyStatement : Nat -> Nat -> List String -> List String
    everyStatement Z _ ps = ps
    everyStatement (S fuel) i ps = case drop i ps of
      [] => ps
      _ => case chooseBreak limit True ps i of
             Just b => everyStatement fuel (S i) (split i b ps)
             Nothing => everyStatement (S fuel) (S i) ps

    -- the pieces from the `i`th on broken until they fit
    go : Nat -> Nat -> List String -> List String
    go Z _ ps = ps
    go (S fuel) i ps = case drop i ps of
      [] => ps
      (p :: _) =>
        if width p <= limit then go (S fuel) (S i) ps else
          case chooseBreak limit False ps i of
            Just b => let ps' =
                            split i b ps in go fuel i
                              (if b.statement then statementsFrom fuel (S i) ps' else ps')
            Nothing => go (S fuel) (S i) ps

||| `reflow-lines`: each line wider than the width (`--arg WIDTH`, 100 by
||| default) broken into lines that fit.
export
reflowLines : (arguments : List String) -> Refactoring
reflowLines args =
  Refactoring.fileRefactoring "reflow-lines"
    "break each line wider than a width (--arg WIDTH, 100 by default) into lines that fit"
      candidates
  where
    limit : Int
    limit = case args of
      [w] => maybe 100 id (parsePositive w)
      _ => 100

    comment : String -> Bool
    comment l = isPrefixOf "--" (ltrim l) || isPrefixOf "|||" (ltrim l)

    -- each wide line that breaks, where it is, with its pieces
    wide : Subject -> List (Int, String, List String)
    wide s = mapMaybe one (zip [0 .. length (Subject.linesOf s)] (Subject.linesOf s))
      where
        one : (Nat, String) -> Maybe (Int, String, List String)
        one (i, l) =
          if width l <= limit || comment l then Nothing
          else case trailingComment l of
            -- wide for its comment alone: the comment above, the code whole
            Just (code, note) =>
              if width code <= limit
                 then Just (cast i, l, [pack (takeWhile (== ' ') (unpack l)) ++ note, code])
                 else map (cast i, l,) (reflow limit l)
            Nothing => map (cast i, l,) (reflow limit l)

    candidates : Subject -> List Refactoring.Candidate
    candidates s = case wide s of
      [] => []
      ws =>
        Refactoring.candidate ("lines wider than " ++ show limit)
          (Right (Change.inFile s.file.path [ Edit.replaceLines i i ps | (i, _, ps) <- ws ]))
            ::
              [ Refactoring.candidate ("`" ++ trim l ++ "`") (Right (Change.inFile s.file.path [Edit.replaceLines i i ps]))
               | (i, l, ps) <- ws ]
