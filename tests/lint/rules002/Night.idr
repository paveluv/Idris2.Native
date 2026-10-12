||| Where the two `hoot`s meet, each written with its namespace, so a reader
||| knows which.
module Night

import Bat
import Owl

%default total

||| The night's calls.
export
night : List String
night = [Owl.hoot MkOwl, Bat.hoot MkBat]
