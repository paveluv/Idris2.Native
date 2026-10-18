#!/bin/sh
# Differential oracle for the native backend.
#
# Compiles and runs each program under two code generators, the subject
# (default `native`) and the oracle (default `chez`, Idris's own code
# generator; `vmcode-interp`, the interpreter of the VMCode that the native
# backend compiles, lacks some of the foreign functions the programs
# reach), and reports
# per program whether their standard output and exit status agree. Nothing
# here is in the product path: the oracle is a test-time tool.
#
# Usage: oracle.sh IDRIS2 [OPTION]... PROGRAM.idr...
#
#   --subject CG            the code generator under test (default native)
#   --oracle CG             the reference (default chez)
#   --cont heap|stack       the subject's lowering of continuations, passed
#                           as `--directive cont=...`; with `--oracle native
#                           --oracle-directive cont=heap` it compares the two
#                           lowerings with each other
#   --nursery BYTES         the subject's allocation window, passed as
#                           `--directive nursery=...`; a tiny window makes
#                           allocation-heavy programs take the slow path, and,
#                           once the runtime collects, collect inside
#                           primitives
#   --val-encoding E        the subject's encoding of uniform values, tag1
#                           (the default), tag0 or nofixnums, passed as
#                           `--directive val-encoding=...`
#   --subject-directive D   pass `--directive D` to the subject
#   --oracle-directive D    pass `--directive D` to the oracle
#   --timeout SECONDS       per run, when `timeout` is available (default 60)
#   --separate              compile each program on its own, as a program of
#                           its own, rather than all of them in one (also
#                           ORACLE_SEPARATE=1)
#
# By default the programs are compiled together, once under each code
# generator: each becomes a module P<name>, its directives' `Main.` its
# own, its `main` exported as `run`, and a driver `Main` runs the one its first
# argument names. Each still runs as a process of its own, with its own
# output and exit status, so a program that ends early, or reaches what
# the native backend does not lower, ends only its own run; a program that
# does not compile fails the whole compilation, and every program reports
# that error. vmcode-interp runs `main` without arguments, so under it the
# programs are compiled separately.
#
# The compilations and runs go on in parallel, ORACLE_JOBS of them at a
# time (default 16), each in its own work directory; the report is written
# after them all, in the order the programs are given.
#
# A program is a `module Main`; its behaviour is its standard output and its
# exit status. The native backend does not lower output yet, so the programs
# named Status* report through their exit status alone: each folds what it
# computes, or the number of its checks that fail, into the status, which
# the system keeps modulo 256. The others print, and stay unsupported under
# the native backend until it lowers output. The report has one line per
# program, then a summary:
#
#   agree          the same standard output and exit status
#   MISMATCH       they differ; the differences follow, indented
#   unsupported    the native program reached a construct the backend does
#                  not lower yet: exit status 70 and `idris: unsupported: `,
#                  then which construct and in which function
#   oracle error   the oracle failed to compile the program or to run it; its
#                  first error line follows. vmcode-interp reports a runtime
#                  error on standard output with exit status 0, so a line
#                  starting `Error:` there is what counts, and a program
#                  checked against it must not print such a line itself
#   subject error  the subject failed to compile the program
#   timeout        a run took longer than the limit
#
# Work files go to ./build/oracle/<program>/<side>.

set -u

if [ $# -lt 1 ]; then
  echo "usage: oracle.sh IDRIS2 [OPTION]... PROGRAM.idr..." >&2
  exit 2
fi
idris2=$1
shift

subject=native
oracle=chez
subject_dirs=""
oracle_dirs=""
limit=60
separate=${ORACLE_SEPARATE:-0}

while [ $# -gt 0 ]; do
  case $1 in
    --subject) subject=$2; shift 2 ;;
    --oracle) oracle=$2; shift 2 ;;
    --cont) subject_dirs="$subject_dirs --directive cont=$2"; shift 2 ;;
    --nursery) subject_dirs="$subject_dirs --directive nursery=$2"; shift 2 ;;
    --val-encoding) subject_dirs="$subject_dirs --directive val-encoding=$2"; shift 2 ;;
    --subject-directive) subject_dirs="$subject_dirs --directive $2"; shift 2 ;;
    --oracle-directive) oracle_dirs="$oracle_dirs --directive $2"; shift 2 ;;
    --timeout) limit=$2; shift 2 ;;
    --separate) separate=1; shift ;;
    --) shift; break ;;
    -*) echo "oracle.sh: unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

if command -v timeout > /dev/null 2>&1; then
  limited() { timeout "$limit" "$@"; }
else
  limited() { "$@"; }
fi

flags="--no-banner --no-color --console-width 0"

# side CG DIRECTIVES DIR: compile and run DIR/Main.idr under CG. Leaves
# DIR/log (the compiler's messages), DIR/out, DIR/err and DIR/status, which
# is the exit status, or "compile" if compilation failed.
side() {
  cg=$1 dirs=$2 dir=$3
  (
    cd "$dir" || exit 1
    : > out
    : > err
    if [ "$cg" = vmcode-interp ]; then
      # Check first, so that compiler messages stay out of the program's
      # output; executing then loads the checked module silently.
      # shellcheck disable=SC2086
      "$idris2" $flags --check Main.idr > log 2>&1
      if grep -q '^Error:' log; then echo compile > status; exit 0; fi
      # shellcheck disable=SC2086
      limited "$idris2" $flags --cg "$cg" $dirs Main.idr -x main > out 2> err
      echo $? > status
    else
      # shellcheck disable=SC2086
      "$idris2" $flags --cg "$cg" $dirs Main.idr -o prog > log 2>&1
      if grep -q '^Error:' log || [ ! -x build/exec/prog ]; then echo compile > status; exit 0; fi
      limited ./build/exec/prog > out 2> err
      echo $? > status
    fi
  )
}

# combined CG DIRECTIVES DIR PROGRAM...: the programs as modules of one
# driver in DIR, compiled under CG. Leaves DIR/log, and DIR/status: "compile"
# if compilation failed, else empty.
combined() {
  cg=$1 dirs=$2 dir=$3
  shift 3
  mkdir -p "$dir"
  {
    echo "module Main"
    echo "import System"
    for src in "$@"; do echo "import P$(basename "$src" .idr)"; done
    # a program may be partial, so the driver is
    echo "partial"
    echo "main : IO ()"
    echo "main = do"
    echo "  args <- getArgs"
    echo "  case args of"
    for src in "$@"; do
      p=$(basename "$src" .idr)
      echo "    [_, \"$p\"] => P$p.run"
    done
    echo "    _ => putStrLn \"oracle: no such program\""
  } > "$dir/Main.idr"
  for src in "$@"; do
    p=$(basename "$src" .idr)
    sed -e "s/^module Main\$/module P$p/" -e "/^%cg/s/Main\./P$p./g" -e "s/^main : IO ()\$/export\nrun : IO ()/" -e "s/^main\b/run/" \
      "$src" > "$dir/P$p.idr"
  done
  (
    cd "$dir" || exit 1
    # shellcheck disable=SC2086
    "$idris2" $flags --cg "$cg" $dirs Main.idr -o prog > log 2>&1
    if grep -q '^Error:' log || [ ! -x build/exec/prog ]; then echo compile > status; else : > status; fi
  )
}

# run DIR NAME WORK: the program NAME of the driver compiled in DIR, run with
# WORK as the directory it runs in, leaving WORK/out, WORK/err and
# WORK/status as `side` does; WORK/log the compilation's.
run() {
  dir=$1 name=$2 work=$3
  cp "$dir/log" "$work/log"
  if [ "$(cat "$dir/status")" = compile ]; then echo compile > "$work/status"; return; fi
  (
    cd "$work" || exit 1
    limited "$dir/build/exec/prog" "$name" > out 2> err
    echo $? > status
  )
}

first_error() {
  grep -m 1 '^Error:' "$1" | cut -c 1-160
}

n=0 agree=0 unsupported=0 mismatch=0 errors=0 timeouts=0

if [ "$oracle" = vmcode-interp ] || [ "$subject" = vmcode-interp ]; then separate=1; fi

# Both sides of every program, ORACLE_JOBS at a time: each compilation or run
# is a job in the background, and a full batch is waited for before the next
# starts.
jobs=${ORACLE_JOBS:-16}
running=0
if [ "$separate" = 0 ]; then
  rm -rf build/oracle/combined
  combined "$oracle" "$oracle_dirs" "$PWD/build/oracle/combined/oracle" "$@" &
  combined "$subject" "$subject_dirs" "$PWD/build/oracle/combined/subject" "$@" &
  wait
fi
for src in "$@"; do
  name=$(basename "$src" .idr)
  work=build/oracle/$name
  rm -rf "$work"
  mkdir -p "$work/oracle" "$work/subject"
  if [ "$separate" = 0 ]; then
    run "$PWD/build/oracle/combined/oracle" "$name" "$work/oracle" &
    run "$PWD/build/oracle/combined/subject" "$name" "$work/subject" &
  else
    cp "$src" "$work/oracle/Main.idr"
    cp "$src" "$work/subject/Main.idr"
    side "$oracle" "$oracle_dirs" "$work/oracle" &
    side "$subject" "$subject_dirs" "$work/subject" &
  fi
  running=$((running + 2))
  if [ "$running" -ge "$jobs" ]; then
    wait
    running=0
  fi
done
wait

for src in "$@"; do
  name=$(basename "$src" .idr)
  work=build/oracle/$name
  os=$(cat "$work/oracle/status")
  ss=$(cat "$work/subject/status")
  n=$((n + 1))
  if [ "$os" = compile ]; then
    echo "$name: oracle error: $(first_error "$work/oracle/log")"
    errors=$((errors + 1))
  elif [ "$oracle" = vmcode-interp ] && grep -q '^Error:' "$work/oracle/out"; then
    echo "$name: oracle error: $(first_error "$work/oracle/out")"
    errors=$((errors + 1))
  elif [ "$ss" = compile ]; then
    echo "$name: subject error: $(first_error "$work/subject/log")"
    errors=$((errors + 1))
  elif [ "$subject" = native ] && [ "$ss" = 70 ] && grep -q '^idris: unsupported: ' "$work/subject/err"; then
    echo "$name: unsupported"
    unsupported=$((unsupported + 1))
  elif [ "$os" = 124 ] || [ "$ss" = 124 ]; then
    echo "$name: timeout"
    timeouts=$((timeouts + 1))
  elif cmp -s "$work/oracle/out" "$work/subject/out" && [ "$os" = "$ss" ]; then
    echo "$name: agree"
    agree=$((agree + 1))
  else
    echo "$name: MISMATCH"
    diff "$work/oracle/out" "$work/subject/out" | sed 's/^/    /'
    if [ "$os" != "$ss" ]; then
      echo "    exit status: $oracle $os, $subject $ss"
    fi
    mismatch=$((mismatch + 1))
  fi
done

if [ "$n" = 1 ]; then noun=program; else noun=programs; fi
echo "$n $noun: $agree agree, $unsupported unsupported, $mismatch mismatch, $errors error, $timeouts timeout"
