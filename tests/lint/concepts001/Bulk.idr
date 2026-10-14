||| A module of four concepts, of which its importer uses one: what
||| precision counts against. Its own comment leaves it out of precision,
||| as a module is until its importers are reshaped, and the score names
||| it.
module Bulk

-- lint: exclude precision: the fixture of a module left out

%default total

||| One.
public export
one : Nat
one = 1

||| Two.
public export
two : Nat
two = 2

||| Three.
public export
three : Nat
three = 3

||| All of them.
public export
bulk : List Nat
bulk = [one, two, three]
