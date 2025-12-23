#!/usr/bin/env bash
# Test runner for HVM4
#
# Test format:
#   @main = <expression>
#   //<expected output>
#
# For multi-line expected output, use multiple // lines.
# Tests starting with _ are skipped.

set -uo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
C_BIN="$DIR/../clang/main"
C_MAIN="${C_BIN}.c"

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
    nocollapse=0
    while IFS= read -r line; do
      if [[ "$line" == //* ]]; then
        if [[ "$line" == '//!'* ]]; then
          nocollapse=1
          content="${line#//!}"
        else
          content="${line#//}"
        fi
        [ -n "$expected" ] && expected="${content}"$'\n'"$expected"
        [ -z "$expected" ] && expected="${content}"
        ((nlines++))
      else
        break
      fi
    done < <(tail -r "$test_file" 2>/dev/null || tac "$test_file")

    # For collapse_* and enum_* tests, infer limit from expected output lines
    collapse_count=""
    if [[ "$name" == collapse_* || "$name" == enum_* ]]; then
      collapse_count="$nlines"
    fi

    if [ $nlines -eq 0 ]; then
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

    # Determine flags: all tests use -C by default unless //! is used
    flags=""
    if [ "$nocollapse" -eq 0 ]; then
      flags="-C"
      case "$name" in
        collapse_* | enum_* )
          [ -n "$collapse_count" ] && flags="${flags}${collapse_count}"
          ;;
      esac
    fi

    actual="$("$bin" "$tmp" $flags 2>&1)"

    # Strip ANSI escape codes for comparison
    actual_clean="$(echo "$actual" | sed 's/\x1b\[[0-9;]*m//g')"
    expected_clean="$(echo "$expected" | sed 's/\x1b\[[0-9;]*m//g')"

    # For PARSE_ERROR tests, just check if output starts with PARSE_ERROR
    if [ "$expected_clean" = "PARSE_ERROR" ]; then
      if [[ "$actual_clean" == PARSE_ERROR* ]]; then
        echo "[PASS] $name"
      else
        echo "[FAIL] $name"
        echo "  expected: PARSE_ERROR"
        echo "  detected: $actual_clean"
        status=1
      fi
    elif [ "$actual_clean" = "$expected_clean" ]; then
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

run_tests "$C_BIN" "C" || exit 1

echo "All tests passed!"
exit 0
