||| What a module makes `public export` that only it needs public:
||| `public-unneeded`.
module Mode

import Data.Vect

%default total

||| A mode: `Pace` names the type, but no other module uses its
||| constructors, which `export` would keep here. Reported.
public export
data Mode = Fast | Slow

||| How fast a mode goes.
export
speed : Mode -> Nat
speed Fast = 2
speed Slow = 1

||| A public function no other module uses: its body need not be public.
||| Reported.
public export
slower : Mode -> Nat
slower m = speed m

||| Public, and needed so: `Lanes`, public too, computes with it, and an
||| importer sees `Lanes`'s body. Not reported.
public export
twoLanes : Nat
twoLanes = 2

||| The lanes of a road, computed in importers' types.
public export
Lanes : Type
Lanes = Vect twoLanes Nat
