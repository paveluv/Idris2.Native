||| `Report` writes no name of `Shape`, but showing the canvas uses `Show
||| Shape`, the implementation `Shape` defines, which search finds only
||| because `Canvas` re-exports `Shape`: `import-indirect` too.
module Report

import Canvas

%default total

||| The canvas, shown.
export
report : String
report = show canvas
