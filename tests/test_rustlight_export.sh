#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/clight2rust-export.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

cd "$work"
"$root/ccomp" -drustlight "$root/test/c/sha1.c"
test -s sha1.rs
grep -F '#[path = "ptr.rs"]' sha1.rs >/dev/null
grep -F '#[path = "callback.rs"]' sha1.rs >/dev/null
grep -F '#[path = "stdio.rs"]' sha1.rs >/dev/null
test ! -e a.out
test ! -e sha1.o
test ! -e sha1.s
