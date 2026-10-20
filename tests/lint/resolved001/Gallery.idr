||| `Gallery` writes `Circle`, which `Shape` defines, and imports only
||| `Canvas`, which re-exports `Shape`: `import-indirect`, import `Shape`.
module Gallery

import Canvas

%default total

||| The canvas, and one shape more.
export
gallery : List Shape
gallery = Circle 3 :: Canvas.canvas
