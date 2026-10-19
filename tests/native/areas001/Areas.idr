-- The per-thread areas, sized from the program. A record of 100 fields,
-- built in a loop until the allocation window fills, keeps 100 GC-visible
-- values live across an allocation's slow path, so its rooting stub pushes
-- 100 entries onto ROOTS; summing it needs more than 8192 SCRATCH slots. A
-- call of a function of 340 parameters passes 334 arguments in ARGS.
-- With fixed areas of 64 ROOTS entries, 8192 SCRATCH slots and 256 ARGS
-- words, the first crashed, the second became the abort stub, and the third
-- gave wrong results.
--
-- The areas are memory each thread keeps outside the heap. ROOTS holds the
-- values live across an allocation that may collect, where the collector
-- finds them; SCRATCH holds the values of a function that register
-- allocation does not keep in machine registers, today all of them; ARGS
-- holds the arguments beyond the machine's argument registers, so that no
-- argument travels on the machine stack and a tail call of any arity is a
-- jump. The program exits with 0 when every check holds.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

record Big where
  constructor MkBig
  f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19 : Int
  f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37 : Int
  f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55 : Int
  f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73 : Int
  f74, f75, f76, f77, f78, f79, f80, f81, f82, f83, f84, f85, f86, f87, f88, f89, f90, f91 : Int
  f92, f93, f94, f95, f96, f97, f98, f99 : Int

-- Allocates a record of 100 fields, each a uniform value.
mk : Int -> Big
mk x =
  MkBig (x + 0) (x + 1) (x + 2) (x + 3) (x + 4) (x + 5) (x + 6) (x + 7) (x + 8) (x + 9) (x + 10)
    (x + 11) (x + 12) (x + 13) (x + 14) (x + 15) (x + 16) (x + 17) (x + 18) (x + 19) (x + 20)
      (x + 21) (x + 22) (x + 23) (x + 24) (x + 25) (x + 26) (x + 27) (x + 28) (x + 29) (x + 30)
        (x + 31) (x + 32) (x + 33) (x + 34) (x + 35) (x + 36) (x + 37) (x + 38) (x + 39) (x + 40)
          (x + 41) (x + 42) (x + 43) (x + 44) (x + 45) (x + 46) (x + 47) (x + 48) (x + 49) (x + 50)
            (x + 51) (x + 52) (x + 53) (x + 54) (x + 55) (x + 56) (x + 57) (x + 58) (x + 59)
              (x + 60) (x + 61) (x + 62) (x + 63) (x + 64) (x + 65) (x + 66) (x + 67) (x + 68)
                (x + 69) (x + 70) (x + 71) (x + 72) (x + 73) (x + 74) (x + 75) (x + 76) (x + 77)
                  (x + 78) (x + 79) (x + 80) (x + 81) (x + 82) (x + 83) (x + 84) (x + 85) (x + 86)
                    (x + 87) (x + 88) (x + 89) (x + 90) (x + 91) (x + 92) (x + 93) (x + 94) (x + 95)
                      (x + 96) (x + 97) (x + 98) (x + 99)

sumBig : Big -> Int
sumBig b = b.f0 + b.f1 + b.f2 + b.f3 + b.f4 + b.f5 + b.f6 + b.f7 + b.f8 + b.f9 + b.f10 + b.f11
  + b.f12 + b.f13 + b.f14 + b.f15 + b.f16 + b.f17 + b.f18 + b.f19 + b.f20 + b.f21 + b.f22 + b.f23
  + b.f24 + b.f25 + b.f26 + b.f27 + b.f28 + b.f29 + b.f30 + b.f31 + b.f32 + b.f33 + b.f34 + b.f35
  + b.f36 + b.f37 + b.f38 + b.f39 + b.f40 + b.f41 + b.f42 + b.f43 + b.f44 + b.f45 + b.f46 + b.f47
  + b.f48 + b.f49 + b.f50 + b.f51 + b.f52 + b.f53 + b.f54 + b.f55 + b.f56 + b.f57 + b.f58 + b.f59
  + b.f60 + b.f61 + b.f62 + b.f63 + b.f64 + b.f65 + b.f66 + b.f67 + b.f68 + b.f69 + b.f70 + b.f71
  + b.f72 + b.f73 + b.f74 + b.f75 + b.f76 + b.f77 + b.f78 + b.f79 + b.f80 + b.f81 + b.f82 + b.f83
  + b.f84 + b.f85 + b.f86 + b.f87 + b.f88 + b.f89 + b.f90 + b.f91 + b.f92 + b.f93 + b.f94 + b.f95
  + b.f96 + b.f97 + b.f98 + b.f99

-- Builds a `Big` 30000 times, enough to fill the allocation window and take
-- the slow path that asks for a new one, with the fields of the record being
-- built live across it.
roots : Int -> Int -> Int
roots 0 bad = bad
roots i bad = let b = mk i in
              roots (i - 1) (if sumBig b == 100 * i + 4950 then bad else bad + 1)

-- Not inlined, so each call passes all 340 arguments: six in the machine's
-- word argument registers, the others in ARGS.
%noinline
f : Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int
f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26
  a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50
    a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 a73 a74
      a75 a76 a77 a78 a79 a80 a81 a82 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96 a97
        a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110 a111 a112 a113 a114 a115 a116
          a117 a118 a119 a120 a121 a122 a123 a124 a125 a126 a127 a128 a129 a130 a131 a132 a133 a134
            a135 a136 a137 a138 a139 a140 a141 a142 a143 a144 a145 a146 a147 a148 a149 a150 a151
              a152 a153 a154 a155 a156 a157 a158 a159 a160 a161 a162 a163 a164 a165 a166 a167 a168
                a169 a170 a171 a172 a173 a174 a175 a176 a177 a178 a179 a180 a181 a182 a183 a184 a185
                  a186 a187 a188 a189 a190 a191 a192 a193 a194 a195 a196 a197 a198 a199 a200 a201
                    a202 a203 a204 a205 a206 a207 a208 a209 a210 a211 a212 a213 a214 a215 a216 a217
                      a218 a219 a220 a221 a222 a223 a224 a225 a226 a227 a228 a229 a230 a231 a232
                        a233 a234 a235 a236 a237 a238 a239 a240 a241 a242 a243 a244 a245 a246 a247
                          a248 a249 a250 a251 a252 a253 a254 a255 a256 a257 a258 a259 a260 a261 a262
                            a263 a264 a265 a266 a267 a268 a269 a270 a271 a272 a273 a274 a275 a276
                              a277 a278 a279 a280 a281 a282 a283 a284 a285 a286 a287 a288 a289 a290
                                a291 a292 a293 a294 a295 a296 a297 a298 a299 a300 a301 a302 a303
                                  a304 a305 a306 a307 a308 a309 a310 a311 a312 a313 a314 a315 a316
                                    a317 a318 a319 a320 a321 a322 a323 a324 a325 a326 a327 a328 a329
                                      a330 a331 a332 a333 a334 a335 a336 a337 a338 a339 = a0 * 1000
  + a339

args : Int -> Int -> Int
args 0 bad = bad
args x bad =
  args (x - 1)
    (if f x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
      x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
        x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
          x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
            x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
              x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
                x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x x
                  x x x x x x x x x x x x x x x x x x x x x x x x x x x (x + 1) == x * 1000 + x + 1
     then bad else bad + 1)

main : IO ()
main = exitCode (if roots 30000 0 == 0 && args 1000 0 == 0 then 0 else 1)
