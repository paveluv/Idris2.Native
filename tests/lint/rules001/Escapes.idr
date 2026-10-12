||| Leaving what the typechecker proves, with and without a reason. The first
||| `assert_total` has none and is reported; the second's paragraph starts
||| with its reason and it is not. A suppression without a reason, one of no
||| rule, and one that suppresses nothing are each reported themselves.
module Escapes

%default total

loop : Nat -> Nat
loop n = assert_total (loop n)

-- lint: allow trust-escape: the argument halves, so the calls end
halve : Nat -> Nat
halve n = if n == 0 then 0 else assert_total (halve (div n 2))

-- lint: allow trust-escape:
bare : Nat -> Nat
bare n = assert_total (bare n)

-- lint: allow no-such-rule: a rule that does not exist
two : Nat
two = 2

-- lint: allow trust-escape: nothing in this paragraph escapes
three : Nat
three = 3
