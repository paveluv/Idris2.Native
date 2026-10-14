||| Under the group `Farm`: the module's name and one name it exports begin
||| with the group's, which qualifies them already (`Farm.Hand`,
||| `Farm.tool`): `group-prefix`, a warning. `Farmstead` begins with the
||| letters only, not the word, and is not reported.
module Farm.FarmHand

%default total

||| A farm hand's tool.
export
farmTool : Nat
farmTool = 1

||| A place, its name one word.
export
farmstead : Nat
farmstead = 2
