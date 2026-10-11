-- `Lib.double` comes from Lib's TTC, with the directive that marks it flat.
-- This module marks nothing: its ordinary `main` calls a flat function of
-- another module, which the flat oracle compiles from its flat form, made
-- when this program is compiled.
import Lib

main : IO ()
main = printLn (double 21)
