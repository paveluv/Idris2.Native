||| `Frame` imports `Shape` itself, and `Canvas` too, which re-exports
||| `Shape`; it uses `Shape`'s names and nothing of `Canvas`'s own, so
||| `Canvas` brings nothing the module does not import directly:
||| `import-unused`, a redundant import.
module Frame

import Canvas
import Shape

%default total

||| The square a shape fits in.
export
frame : Shape -> Shape
frame (Shape.Circle r) = Shape.Square (2 * r)
frame s = s
