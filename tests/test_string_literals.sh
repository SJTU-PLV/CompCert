#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cases="$root/tests/string_literals"
work=$(mktemp -d "${TMPDIR:-/tmp}/clight2rust-strings.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

for runtime_file in ptr.rs callback.rs stdio.rs; do
  cp "$root/runtime/$runtime_file" "$work/$runtime_file"
done

for name in read_literal read_literal_twice write_array; do
  cc "$cases/$name.c" -o "$work/$name.c-bin"
  (cd "$work" && "$root/ccomp" -drustlight "$cases/$name.c")
  rustc -Awarnings "$work/$name.rs" -o "$work/$name.rs-bin"
  "$work/$name.c-bin" >"$work/$name.c-out"
  "$work/$name.rs-bin" >"$work/$name.rs-out"
  cmp "$work/$name.c-out" "$work/$name.rs-out"
  grep -F 'Ptr::from_ref_const(&__stringlit_' "$work/$name.rs" >/dev/null
done

# A write through const char * is a C constraint violation.  Reject it before
# Rust generation; do not use undefined string-literal mutation as an oracle.
if (cd "$work" && "$root/ccomp" -drustlight "$cases/reject_const_write.c" \
    >reject.stdout 2>reject.stderr); then
  echo "expected const-string write to be rejected" >&2
  exit 1
fi
test ! -e "$work/reject_const_write.rs"

# The writable array must retain a mutable borrow path.
grep -F 'Ptr::from_ref(&mut message' "$work/write_array.rs" >/dev/null
