||| An owl, which hoots; so does a bat (`Bat`). The two `hoot`s meet in
||| `Night`, which writes each with its namespace: not reported.
module Owl

%default total

||| An owl.
public export
data Owl = MkOwl

||| An owl's call.
export
hoot : Owl -> String
hoot MkOwl = "hoo"
