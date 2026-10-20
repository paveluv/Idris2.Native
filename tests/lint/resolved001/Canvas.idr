||| A module of ours that re-exports `Shape` without being a façade: it
||| defines something of its own. Its importers see `Shape`'s names, but a
||| reader of an importer looking for `Circle` finds no import of `Shape`.
module Canvas

-- lint: allow public-import: the fixture's re-export, which `Gallery` and
-- `Report` lean on
import public Shape

%default total

||| The shapes on the canvas.
export
canvas : List Shape
canvas = [Shape.Circle 1, Shape.Square 2]
