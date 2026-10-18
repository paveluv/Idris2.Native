||| A cat, which speaks; so does a dog (`Dog`). The two `speak`s meet in
||| `Zoo` and in `Pets`, which write `speak` without a namespace: counted
||| against the uniqueness, as one name with two meanings.
module Cat

%default total

||| A cat.
public export
data Cat = MkCat

||| What a cat says.
export
speak : Cat -> String
speak MkCat = "meow"
