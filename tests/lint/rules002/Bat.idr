||| A bat, which hoots too: see `Owl`.
module Bat

%default total

||| A bat.
public export
data Bat = MkBat

||| A bat's call.
export
hoot : Bat -> String
hoot MkBat = "eek"
