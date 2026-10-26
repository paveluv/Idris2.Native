-- Marks of constants whose values need a primitive that the evaluation
-- would compute otherwise than the program computes it, refused in one
-- error that says why of each. The evaluation computes a primitive as
-- Idris's compiler does, by Chez's operations, and where Idris leaves a
-- primitive's meaning open the native program's is another:
--
-- * `reading`, `integer` and `real` cast strings to numbers: Chez reads
--   "1e3" as 1000 and "1/2" as 0.5, where the program reads 0 and 0.0;
-- * `shown` shows a subnormal double, which Chez writes as 1.5e-310|45,
--   and the program as 1.5e-310;
-- * `infinite` and `notANumber` cast an infinity and NaN to integers, at
--   which Chez's casts end the compilation, where the program gives 0;
-- * `growth`, `exp 1.0`, is Chez's from the C library, and the program
--   does not compute it;
-- * `back` and `right` shift by negative counts, which Chez makes the
--   other way, 4 shifted left by -1 as 2 and 1 shifted right by -70 as
--   2^70, where the program ends and gives 0; and `wide` shifts a Bits64
--   by 64, which Chez makes as a shift of an Integer, so that a larger
--   count could take more memory than the compilation has.
--
-- The counts are cast from `Int`, which Idris does not fold as it builds
-- the module, so that the shifts are left for the evaluation to compute.
module Differs

%cg native static Differs.reading Differs.integer Differs.real Differs.shown
%cg native static Differs.infinite Differs.notANumber Differs.growth
%cg native static Differs.back Differs.right Differs.wide

reading : Int
reading = cast "1e3"

integer : Integer
integer = cast "1e3"

real : Double
real = cast "1/2"

shown : String
shown = show 1.5e-310

infinite : Int
infinite = cast (1.0 / 0.0)

notANumber : Integer
notANumber = cast (0.0 / 0.0)

growth : Double
growth = exp 1.0

back : Integer
back = prim__shl_Integer 4 (cast (the Int (-1)))

right : Int
right = prim__shr_Int 1 (cast (the Integer (-70)))

wide : Bits64
wide = prim__shl_Bits64 1 (cast (the Int 64))

main : IO ()
main = do
  printLn (reading, integer, real)
  putStrLn shown
  printLn (infinite, notANumber, growth)
  printLn (back, right, wide)
