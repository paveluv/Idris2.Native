#!/bin/sh
# Where self-hosting stands: idris2-native compiled by itself, the census of
# what that compilation could not lower, and the ladder of what the result
# can do.
#
# Usage: selfhost.sh IDRIS2-NATIVE BUILD-DIR
#
# 1. idris2-native compiles its own package with the native code generator,
#    into BUILD-DIR/exec, reading the TTCs of the given build (copied into
#    BUILD-DIR, so that the build of the product stays untouched), with the
#    IR dumped.
# 2. The census: the abort stubs in the IR, by the construct each stands
#    for, the most frequent first. A construct the backend does not lower
#    becomes a stub, so the program always links, and fails only if it gets
#    there.
# 3. The ladder: the natively compiled compiler run on a sequence of tasks,
#    each harder than the last, until one fails. A failure prints the first
#    lines of its standard error, which for a stub names the construct and
#    the function it is in.
#
# On demand, as `make scaling` is, not part of the gate: it takes a minute.

set -u
native=$1
out=$2
here=$(cd "$(dirname "$0")" && pwd)
product=$(cd "$here/../.." && pwd)

mkdir -p "$out"
rm -rf "$out/ttc" "$out/exec"
cp -a "$product/build/ttc" "$out/ttc"

start=$(date +%s)
if ! (cd "$product" && "$native" --build-dir "$out" --output-dir "$out/exec" --cg native \
        --directive "dump-ir=$out/ir" --build idris2-native.ipkg > "$out/build.log" 2>&1); then
  echo "the native compilation of idris2-native failed:"
  tail -20 "$out/build.log"
  exit 1
fi
image="$out/exec/idris2-native"
echo "idris2-native compiled natively in $(( $(date +%s) - start )) s: $(wc -c < "$image") bytes"

echo
echo "abort stubs, by construct:"
grep -o 'Unsupported "[^"]*"' "$out/ir" | sed -e 's/^Unsupported "//' -e 's/"$//' \
  | sort | uniq -c | sort -k1,1nr -k2 | sed 's/^/  /'
echo "  $(grep -c 'Unsupported "' "$out/ir") in all"

echo
echo "the ladder:"
work="$out/ladder"
rm -rf "$work"
mkdir -p "$work"
cp "$here"/*.idr "$work"
# one step: its name, then the command, run in the work directory
step() {
  name=$1
  shift
  if (cd "$work" && timeout 120 "$@" > "$work/step.out" 2> "$work/step.err"); then
    echo "  ok      $name"
  else
    echo "  FAILED  $name (status $?)"
    head -5 "$work/step.err" | sed 's/^/          /'
    head -5 "$work/step.out" | sed 's/^/          /'
    exit 0
  fi
}
step "--version" "$image" --version
step "--check a module without the Prelude" "$image" --no-prelude --check Builtins.idr
step "--check a module with the Prelude" "$image" --check WithPrelude.idr
step "--check a module importing base" "$image" --check WithBase.idr
step "compile a program with the Prelude, natively" "$image" --cg native -o withprelude WithPrelude.idr
step "run it" "$work/build/exec/withprelude"
echo "  (next: idris2-native building itself)"
