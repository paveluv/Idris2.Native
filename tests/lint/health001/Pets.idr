||| A second place where the two `speak`s meet without a namespace: the name's
||| offender lists every module where it meets, so that each can qualify
||| one at once.
module Pets

import Cat
import Dog

%default total

||| What the pets say, the dog first.
export
pets : List String
pets = [speak MkDog, speak MkCat]
