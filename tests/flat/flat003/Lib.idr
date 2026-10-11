-- A library's flat function. The directive belongs to the module that
-- defines the function, and Idris keeps it in the module's TTC, so every
-- program that imports the module sees the function as flat.
module Lib

%cg native flat Lib.double
export
double : Bits64 -> Bits64
double x = x + x
