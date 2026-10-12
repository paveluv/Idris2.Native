||| A cat, which speaks; so does a dog (`Dog`). The two `speak`s meet in
||| `Zoo`, which writes `speak` without a namespace: reported, here and in
||| `Dog`, as one name with two meanings.
module Cat

%default total

||| A cat.
public export
data Cat = MkCat

||| What a cat says.
export
speak : Cat -> String
speak MkCat = "meow"
