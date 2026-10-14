||| Where a source location is in the lines of its file: the lines it spans
||| (`lineSpan`), the column it starts at (`startColumn`), and its two ends
||| (`bounds`).
module Lint.Refactor.Span

import Core.FC

%default covering

||| The lines a source location spans, from its first to its last.
export
lineSpan : FC -> (Int, Int)
lineSpan (MkFC _ (sl, _) (el, _)) = (sl, el)
lineSpan (MkVirtualFC _ (sl, _) (el, _)) = (sl, el)
lineSpan EmptyFC = (-1, -1)

||| The column a source location starts at.
export
startColumn : FC -> Int
startColumn (MkFC _ (_, sc) _) = sc
startColumn (MkVirtualFC _ (_, sc) _) = sc
startColumn EmptyFC = 0

||| Where a source location starts and where it ends, each a line and a
||| column, the end past its last character; a location with no place has
||| neither.
export
bounds : FC -> Maybe ((Int, Int), (Int, Int))
bounds (MkFC _ s e) = Just (s, e)
bounds (MkVirtualFC _ s e) = Just (s, e)
bounds EmptyFC = Nothing
