#!/usr/bin/env bash
set -uo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
HS_BIN="$DIR/../haskell/main"
C_BIN="$DIR/../clang/main"
HS_MAIN="${HS_BIN}.hs"
C_MAIN="${C_BIN}.c"

# Build Haskell
if [ ! -f "$HS_MAIN" ]; then
  echo "error: expected Haskell entrypoint at $HS_MAIN" >&2
  exit 1
fi
(cd "$DIR/../haskell" && ghc -O2 -o main main.hs)

# Build C
if [ ! -f "$C_MAIN" ]; then
  echo "error: expected C entrypoint at $C_MAIN" >&2
  exit 1
fi
(cd "$DIR/../clang" && clang -O2 -o main main.c)

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

run_tests() {
  local bin="$1"
  local label="$2"
  local status=0

  echo "=== Testing $label ==="
  for test_file in "${tests[@]}"; do
    name="$(basename "${test_file%.hvm4}")"

    # Extract trailing // comment lines (consecutive from end of file)
    expected=""
    nlines=0
    while IFS= read -r line; do
      if [[ "$line" == //* ]]; then
        [ -n "$expected" ] && expected="${line#//}"$'\n'"$expected"
        [ -z "$expected" ] && expected="${line#//}"
        ((nlines++))
      else
        break
      fi
    done < <(tail -r "$test_file" 2>/dev/null || tac "$test_file")

    if [ -z "$expected" ]; then
      echo "[FAIL] $name (missing expected result comment)" >&2
      status=1
      continue
    fi

    # Create temp file without the trailing // comment lines
    tmp="$(mktemp "${DIR}/.tmp.${name}.XXXXXX")"
    tmp_files+=("$tmp")
    total=$(wc -l < "$test_file")
    keep=$((total - nlines))
    head -n "$keep" "$test_file" > "$tmp"

    # Tests starting with "collapse_" or "enum_" need -C flag
    flags=""
    case "$name" in
      collapse_* | enum_* ) flags="-C" ;;
    esac

    actual="$("$bin" "$tmp" $flags)"

    if [ "$actual" = "$expected" ]; then
      echo "[PASS] $name"
    else
      echo "[FAIL] $name"
      echo "  expected: $expected"
      echo "  detected: $actual"
      status=1
    fi
  done
  echo ""
  return $status
}

hs_status=0
c_status=0

run_tests "$HS_BIN" "Haskell" || hs_status=1
run_tests "$C_BIN" "C" || c_status=1

if [ $hs_status -eq 0 ] && [ $c_status -eq 0 ]; then
  echo "All tests passed for both implementations!"
  exit 0
else
  echo "Some tests failed."
  exit 1
fi
