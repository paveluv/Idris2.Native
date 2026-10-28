#!/bin/sh
# The native backend's phases against the size of the program, to find any
# whose time grows faster than the program.
#
# Usage: scaling.sh IDRIS2-NATIVE [SIZE]...   (default 128 256 512 1024)
#
# Each shape is a program of n units, for each size n:
#
#   functions  a chain of n functions, each calling the next
#   straight   one function of n dependent operations (an inlined function
#              applied n times)
#   joins      one function of n operations, each with a branch that meets
#              again after it (a join point), on a parameter of the function
#   calls      one function of n calls, each result passed to the next
#   flat       a flat function of n dependent operations
#   case       a function of n constructors' alternatives
#   literals   a function of n alternatives, each a string literal
#   constlist  a constant list of n string literals
#
# Each is built of nested applications, which Idris typechecks in time
# linear in n (a `let` block or a `do` block of n statements takes it a
# minute at n = 512). An inlined helper uses its argument once: Idris inlines
# a function by writing its argument at each use, so a helper that used it
# twice, nested n deep, would be 2^n long. Each is typechecked first, then
# compiled natively under
# `--timing 2`, which the backend answers with the time of each of its
# phases, then run.
#
# A phase's time is its own work: the backend reports, with each phase, the
# part of its time the collector took, which follows where collections fall
# (one landing in a phase at n can triple its time and miss it at 2n), and
# that part is left out. A phase is superlinear when, from a quarter of the
# largest size to the largest, its time grows more than eightfold and
# reaches 20 ms: linear work grows fourfold, n log n a little more,
# quadratic work sixteenfold. Each doubling is printed too.
# Where the time test is unsure, Chez's profiler is exact: a program built
# with `--profile` counts every expression, and two profiles at n and 2n,
# compared function by function, show twice the count for linear work and
# four times for quadratic. Idris's own passes are reported, not checked.
#
# The exit status is 1 if a phase is superlinear that is not in KNOWN, or
# if one in KNOWN no longer is: then it is fixed, and comes out of KNOWN.
# The sizes are ascending, each twice the one before, at least three.
# Work files go to ./build/<shape>-<n>.

set -u

if [ $# -lt 1 ]; then
  echo "usage: scaling.sh IDRIS2-NATIVE [SIZE]..." >&2
  exit 2
fi
idris2=$1
shift
sizes=${*:-128 256 512 1024}

# Superlinear phases known and accepted for now, as shape:phase, separated
# by spaces: none.
KNOWN=""

shapes=${SHAPES:-"functions straight joins calls flat case literals constlist"}

# The program of a shape at size n, on standard output.
program() {
  awk -v shape="$1" -v n="$2" '
    function nested(f, x,    i, s) {
      s = ""
      for (i = 0; i < n; i++) s = s f " ("
      s = s x
      for (i = 0; i < n; i++) s = s ")"
      return s
    }
    BEGIN {
      print "module Main"; print ""
      if (shape == "functions") {
        for (i = n - 1; i >= 0; i--) {
          print "%noinline"; print "f" i " : Int -> Int"
          if (i + 1 < n) print "f" i " x = f" (i + 1) " (x + " i ")"
          else print "f" i " x = x + " i
          print ""
        }
        print "main : IO ()"; print "main = if f0 1 == 0 then pure () else pure ()"
      } else if (shape == "straight" || shape == "calls") {
        print (shape == "calls" ? "%noinline" : "%inline")
        print "s : Int -> Int"; print "s y = y * 3 + 1"
        print ""; print "%noinline"; print "g : Int -> Int"
        print "g x = " nested("s", "x")
        print ""; print "main : IO ()"; print "main = if g 1 == 0 then pure () else pure ()"
      } else if (shape == "joins") {
        print "%inline"; print "s : Bool -> Int -> Int"; print "s c y = y * 3 + (if c then 1 else 2)"
        print ""; print "%noinline"; print "g : Bool -> Int -> Int"
        print "g c x = " nested("s c", "x")
        print ""; print "main : IO ()"; print "main = if g True 1 == 0 then pure () else pure ()"
      } else if (shape == "flat") {
        print "%inline"; print "s : Bits64 -> Bits64"; print "s y = y * 3 + 1"; print ""
        print "%cg native flat Main.g"; print "g : Bits64 -> Bits64"
        print "g x = " nested("s", "x")
        print ""; print "main : IO ()"; print "main = if g 1 == 0 then pure () else pure ()"
      } else if (shape == "case") {
        print "data E"; print "  = C0"
        for (i = 1; i < n; i++) print "  | C" i
        print ""; print "%noinline"; print "mk : Int -> E"; print "mk i = if i < 0 then C0 else C1"
        print ""; print "h : E -> Int"
        for (i = 0; i < n; i++) print "h C" i " = " i
        print ""; print "main : IO ()"; print "main = if h (mk 1) == 0 then pure () else pure ()"
      } else if (shape == "literals") {
        print "%noinline"; print "lit : Int -> String"
        for (i = 0; i < n; i++) print "lit " i " = \"s" i "\""
        print "lit _ = \"\""
        print ""; print "main : IO ()"; print "main = if length (lit 5) == 0 then pure () else pure ()"
      } else if (shape == "constlist") {
        print "%noinline"; print "strs : List String"; print "strs ="
        print "  [ \"s0\""
        for (i = 1; i < n; i++) print "  , \"s" i "\""
        print "  ]"
        print ""; print "main : IO ()"; print "main = if length strs == 0 then pure () else pure ()"
      }
    }'
}

results=./build/results
mkdir -p ./build
: > "$results"

echo "milliseconds per phase, without the collector's part"
printf '%-10s %5s %8s %8s %8s %8s %8s %8s %8s %8s\n' \
  shape n runtime idris flatin lower regs render link write
for shape in $shapes; do
  for n in $sizes; do
    dir=./build/$shape-$n
    mkdir -p "$dir"
    program "$shape" "$n" > "$dir/Main.idr"
    ( cd "$dir" && "$idris2" --check Main.idr > check.log 2>&1 ) || {
      echo "$shape $n: does not typecheck, see $dir/check.log"; exit 1; }
    ( cd "$dir" && "$idris2" --cg native --timing 2 -o m Main.idr > compile.log 2>&1 ) || {
      echo "$shape $n: does not compile, see $dir/compile.log"; exit 1; }
    ( cd "$dir" && ./build/exec/m ) || { echo "$shape $n: the program fails"; exit 1; }
    awk -v shape="$shape" -v n="$n" '
      # TIMING ++ native: <phase>: <total>s (collecting <part>s)
      /TIMING \+\+ native: / {
        sub(/.*native: /, "")
        gc = 0
        if (match($0, /\(collecting [0-9.]+s\)/)) {
          gc = substr($0, RSTART + 12, RLENGTH - 14)
          $0 = substr($0, 1, RSTART - 2)
        }
        t = $NF; sub(/s$/, "", t)
        name = $0; sub(/: [0-9.]+s$/, "", name)
        t = t - gc
        key = ""
        if (name == "the runtime loaded") key = "runtime"
        else if (name == "Idris'"'"'s passes") key = "idris"
        else if (name == "flat inputs") key = "flatin"
        else if (name == "lowering") key = "lower"
        else if (name == "register allocation") key = "regs"
        else if (name == "rendering") key = "render"
        else if (name == "linking") key = "link"
        else if (name == "the image written") key = "write"
        if (key != "") print shape, n, key, int(t * 1000 + 0.5)
      }' "$dir/compile.log" >> "$results"
    awk -v shape="$shape" -v n="$n" '
      $1 == shape && $2 == n { ms[$3] = $4 }
      END {
        printf "%-10s %5d %8d %8d %8d %8d %8d %8d %8d %8d\n", shape, n,
          ms["runtime"], ms["idris"], ms["flatin"], ms["lower"],
          ms["regs"], ms["render"], ms["link"], ms["write"]
      }' "$results"
  done
done

# Each checked phase of each shape: every doubling, printed; the largest
# size against a quarter of it, checked.
awk -v known="$KNOWN" -v sizes="$sizes" '
  BEGIN {
    nk = split(known, ks, " "); for (i = 1; i <= nk; i++) isKnown[ks[i]] = 1
    ns = split(sizes, sz, " ")
    np = split("runtime flatin lower regs render link write", phases, " ")
  }
  { ms[$1 " " $2 " " $3] = $4; shapes[$1] = 1 }
  END {
    if (ns < 3) { print "give at least three sizes, each twice the one before"; exit 2 }
    status = 0
    for (shape in shapes) for (p = 1; p <= np; p++) {
      phase = phases[p]; key = shape ":" phase
      line = ""
      for (i = 1; i <= ns; i++) line = line " " ms[shape " " sz[i] " " phase]
      a = ms[shape " " sz[ns - 2] " " phase]; b = ms[shape " " sz[ns] " " phase]
      super = (b >= 20 && b > 8 * a)
      if (super)
        printf "%s %s: %d ms at n = %d, %d ms at n = %d (each doubling:%s)\n", \
          (isKnown[key] ? "known superlinear:" : "SUPERLINEAR:"), key, a, sz[ns - 2], b, sz[ns], line
      if (super && !isKnown[key]) status = 1
      # a known one counts as fixed only where it was measurable
      if (!super && isKnown[key]) {
        if (b >= 20) {
          printf "%s is no longer superlinear: take it out of KNOWN\n", key; status = 1
        } else printf "%s not measured: under 20 ms at these sizes\n", key
      }
    }
    if (status == 0) print "no phase superlinear beyond the known ones"
    exit status
  }' "$results"
