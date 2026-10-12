||| Where the two `speak`s meet, written without a namespace: a reader has to
||| work out which one each use means.
module Zoo

import Cat
import Dog

%default total

||| Every animal's word.
export
zoo : List String
zoo = [speak MkCat, speak MkDog]
