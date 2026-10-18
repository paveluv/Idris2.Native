||| A dog, which speaks too: see `Cat`.
module Dog

%default total

||| A dog.
public export
data Dog = MkDog

||| What a dog says.
export
speak : Dog -> String
speak MkDog = "woof"
