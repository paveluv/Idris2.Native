||| Names taken from our modules, written bare or under an alias. After
||| `qualify-names` each is written with its module's path past what it
||| shares with `Plan`, nothing at the top: `Geo.Shape.Circle`,
||| `Geo.Shape.area`, `Left.Side.width`. The type `Shape`, named after its
||| module, is `Geo.Shape`, which needs `Geo.Shape` imported as `Geo`;
||| the `Side` modules need no alias, and lose theirs. The Prelude's
||| `length`, which `Geo.Shape` exports too, is left as written.
module Plan

import Geo.Shape
import Left.Side as Left
import Right.Side as Right

%default total

export
plan : Shape -> Nat
plan s = area (Circle (Left.width + Right.width)) + area s + length [the Nat 1]

||| Patterns are names written too: `Geo.Shape.Square _`. A line made
||| longer moves the lines that hang off it, the rest of its `do` block,
||| which would not parse otherwise.
export
corners : Shape -> IO Nat
corners (Square _) = pure 4
corners s = case s of
  Circle r => do putStrLn "none"
                 pure r
  _ => pure 0
