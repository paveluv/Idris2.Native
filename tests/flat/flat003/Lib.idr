module Lib

%cg native flat Lib.double
export
double : Bits64 -> Bits64
double x = x + x
