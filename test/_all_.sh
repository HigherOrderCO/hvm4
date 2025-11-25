#!/usr/bin/env bash
set -uo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$DIR/../haskell/main"
HS_MAIN="${BIN}.hs"

if [ ! -f "$HS_MAIN" ]; then
  echo "error: expected Haskell entrypoint at $HS_MAIN" >&2
  exit 1
fi

(cd "$DIR/../haskell" && ghc -O2 -o main main.hs)

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
  args=""
  expected=""

  args_line="$(grep '^//[[:space:]]*ARGS:' "$test_file" || true)"
  if [ -n "$args_line" ]; then
    args="${args_line#*ARGS:}"
    args="${args#"${args%%[![:space:]]*}"}"
    args="${args%"${args##*[![:space:]]}"}"
  fi

  if grep -q '^//[[:space:]]*EXPECT:' "$test_file"; then
    in_expect=false
    while IFS='' read -r line; do
      if [[ "$line" =~ ^//[[:space:]]*EXPECT: ]]; then
        in_expect=true
        inline="${line#*EXPECT:}"
        inline="${inline#"${inline%%[![:space:]]*}"}"
        inline="${inline%"${inline##*[![:space:]]}"}"
        if [ -n "$inline" ]; then
          expected+="$inline"
        fi
      elif $in_expect && [[ "$line" =~ ^// ]]; then
        content="${line#//}"
        content="${content#"${content%%[![:space:]]*}"}"
        content="${content%"${content##*[![:space:]]}"}"
        expected+="${expected:+$'\n'}${content}"
      elif $in_expect; then
        break
      fi
    done < "$test_file"
  else
    expected_line="$(tail -n 1 "$test_file")"
    if [[ "$expected_line" != //* ]]; then
      echo "[FAIL] $name (missing expected result comment)" >&2
      status=1
      continue
    fi
    expected="${expected_line#//}"
  fi

  expected="${expected#"${expected%%[![:space:]]*}"}"
  expected="${expected%"${expected##*[![:space:]]}"}"

  tmp="$(mktemp "${DIR}/.tmp.${name}.XXXXXX")"
  tmp_files+=("$tmp")

  meta_line=""
  if grep -q '^//[[:space:]]*EXPECT:' "$test_file"; then
    meta_line="$(grep -n '^//[[:space:]]*EXPECT:' "$test_file" | tail -1 | cut -d: -f1)"
  else
    meta_line="$(wc -l < "$test_file")"
  fi

  if [ -n "$meta_line" ] && [ "$meta_line" -gt 0 ]; then
    head -n $((meta_line - 1)) "$test_file" > "$tmp"
  else
    sed '$d' "$test_file" > "$tmp"
  fi

  arg_arr=()
  if [ -n "$args" ]; then
    read -r -a arg_arr <<<"$args"
  fi

  if [ ${#arg_arr[@]} -gt 0 ]; then
    actual="$(timeout 10 "$BIN" "$tmp" "${arg_arr[@]}" || true)"
  else
    actual="$(timeout 10 "$BIN" "$tmp" || true)"
  fi

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
