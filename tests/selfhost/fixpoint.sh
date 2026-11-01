#!/bin/sh
# The self-hosting fixed point: idris2-native, compiled natively by the
# hosted compiler (`make selfhost`'s image), builds idris2-native natively
# from no TTCs, into BUILD-DIR/exec. Its image must be byte for byte the
# one it was built with: the compiler compiled by itself compiles itself to
# itself.
#
# Usage: fixpoint.sh IMAGE BUILD-DIR
#
# Prints the build's wall time and the compiler's peak resident memory,
# which the kernel keeps (VmHWM) and this reads while the build runs, and
# whether the image is the fixed point; exits 1 when the build fails or
# the image differs. It reads the product's sources and the prefix as they
# are while it runs, for hours: build nothing in the product meanwhile.
#
# Not part of the gate, and not meant to be: the build takes hours, where
# the gate takes a minute. That may change as the native compiler nears
# the speed of the Chez-built one.

set -u
image=$1
out=$2
here=$(cd "$(dirname "$0")" && pwd)
product=$(cd "$here/../.." && pwd)

if [ ! -x "$image" ]; then
  echo "no natively compiled idris2-native at $image: run make selfhost first"
  exit 1
fi
rm -rf "$out"
mkdir -p "$out"

cd "$product"
start=$(date +%s)
"$image" --build-dir "$out" --output-dir "$out/exec" --cg native \
  --build idris2-native.ipkg > "$out/build.log" 2>&1 &
pid=$!
# the peak so far, in kB, every second until the build ends
peak=0
while kill -0 "$pid" 2> /dev/null; do
  hwm=$(sed -n 's/^VmHWM:[[:space:]]*\([0-9]*\) kB$/\1/p' "/proc/$pid/status" 2> /dev/null)
  if [ -n "$hwm" ] && [ "$hwm" -gt "$peak" ]; then peak=$hwm; fi
  sleep 1
done
wait "$pid"
status=$?
secs=$(( $(date +%s) - start ))

echo "idris2-native built itself natively in $secs s" \
  "($(( secs / 3600 )) h $(( secs % 3600 / 60 )) min), peak $(( peak / 1024 )) MB"
if [ "$status" -ne 0 ]; then
  echo "the build failed (status $status):"
  tail -20 "$out/build.log"
  exit 1
fi
if cmp -s "$image" "$out/exec/idris2-native"; then
  echo "its image is the one it was built with: the fixed point"
else
  echo "its image DIFFERS from the one it was built with ($(wc -c < "$out/exec/idris2-native")" \
    "bytes against $(wc -c < "$image"))"
  exit 1
fi
