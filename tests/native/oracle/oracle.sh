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
#
# A program is a `module Main`; its behaviour is its standard output and its
# exit status. The report has one line per program, then a summary:
#
#   agree          the same standard output and exit status
#   MISMATCH       they differ; the differences follow, indented
#   unsupported    the native program reached a construct the backend does
#                  not lower yet: exit status 70 and `idris: unsupported`
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

first_error() {
  grep -m 1 '^Error:' "$1" | cut -c 1-160
}

n=0 agree=0 unsupported=0 mismatch=0 errors=0 timeouts=0

for src in "$@"; do
  name=$(basename "$src" .idr)
  work=build/oracle/$name
  rm -rf "$work"
  mkdir -p "$work/oracle" "$work/subject"
  cp "$src" "$work/oracle/Main.idr"
  cp "$src" "$work/subject/Main.idr"
  side "$oracle" "$oracle_dirs" "$work/oracle"
  side "$subject" "$subject_dirs" "$work/subject"
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
  elif [ "$subject" = native ] && [ "$ss" = 70 ] && grep -q '^idris: unsupported$' "$work/subject/err"; then
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
