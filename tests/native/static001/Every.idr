-- Marks refused in one program: one error says why of each, in the order
-- of the marks. `beyond` reads word 1 of the row at 3, the word at
-- `3 + 1`, of four words: outside the object, where the load gives any
-- word, so the evaluation computes none. `later` reads `beyond`, whose
-- evaluation failed, so it fails as `beyond` did, for its reason: a
-- failure leaves no value behind for a later read to find. `square`
-- takes an argument. `squares` itself is a constant.
module Every

import Native.Types.Bytes

%cg native static Every.squares Every.beyond Every.later Every.square

squares : Bytes
squares = generate 4 (\i => cast (i * i))

beyond : Bits64
beyond = uncheckedWord squares 3 1

later : Bits64
later = beyond + 1

square : Int -> Bits64
square i = uncheckedWord squares i 0

main : IO ()
main = printLn (beyond, later, square 2)
