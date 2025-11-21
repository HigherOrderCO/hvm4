#!/usr/bin/env bash
set -uo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/../haskell/main"
HS_MAIN="${BIN}.hs"

if [ ! -f "$HS_MAIN" ]; then
  echo "error: expected Haskell entrypoint at $HS_MAIN" >&2
  exit 1
fi

if [ ! -x "$BIN" ] || [ "$HS_MAIN" -nt "$BIN" ]; then
  (cd "$DIR/../haskell" && ghc -O2 -o main main.hs)
fi

tmp_files=()
cleanup() {
  if [ ${#tmp_files[@]} -gt 0 ]; then
    rm -f "${tmp_files[@]}"
  fi
}
trap cleanup EXIT

shopt -s nullglob
tests=()
for f in "$DIR"/*.hvm4; do
  name="$(basename "$f")"
  case "$name" in
    _* ) continue ;;
    *  ) tests+=("$f") ;;
  esac
done
shopt -u nullglob

if [ ${#tests[@]} -eq 0 ]; then
  echo "no .hvm4 files found under $DIR" >&2
  exit 1
fi

status=0
for test_file in "${tests[@]}"; do
  name="$(basename "${test_file%.hvm4}")"
  expected_line="$(tail -n 1 "$test_file")"

  if [[ "$expected_line" != //* ]]; then
    echo "[FAIL] $name (missing expected result comment)" >&2
    status=1
    continue
  fi

  expected="${expected_line#//}"

  tmp="$(mktemp "${DIR}/.tmp.${name}.XXXXXX")"
  tmp_files+=("$tmp")
  sed '$d' "$test_file" > "$tmp"

  actual="$("$BIN" "$tmp")"

  if [ "$actual" = "$expected" ]; then
    echo "[PASS] $name"
  else
    echo "[FAIL] $name"
    echo "  expected: $expected"
    echo "  detected: $actual"
    status=1
  fi
done

exit $status
