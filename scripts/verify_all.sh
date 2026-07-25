#!/usr/bin/env bash
set -uo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/verify_all.sh [OPTIONS]

Verify every standalone example in this repository.

Options:
  -t, --target TARGET   Make target to run for each example (default: all)
                       Common targets: all, compile, debug
  -v, --verbose         Stream verifier output for successful examples too
      --fail-fast       Stop at the first failed example
  -h, --help            Show this help message

Examples:
  scripts/verify_all.sh
  scripts/verify_all.sh --target debug
  scripts/verify_all.sh --verbose --fail-fast
USAGE
}

target="all"
verbose=0
fail_fast=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    -t|--target)
      if [[ $# -lt 2 ]]; then
        echo "error: missing value for $1" >&2
        exit 2
      fi
      target="$2"
      shift 2
      ;;
    --target=*)
      target="${1#*=}"
      shift
      ;;
    -v|--verbose)
      verbose=1
      shift
      ;;
    --fail-fast)
      fail_fast=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if ! command -v make >/dev/null 2>&1; then
  echo "error: make is not available on PATH" >&2
  exit 127
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
cd "$repo_root" || exit 1

examples=()
while IFS= read -r -d '' makefile; do
  dir="${makefile%/Makefile}"
  if [[ -f "$dir/main.rs" ]]; then
    examples+=("${dir#./}")
  fi
done < <(find . -mindepth 2 -name Makefile -print0 | sort -z -V)

if [[ ${#examples[@]} -eq 0 ]]; then
  echo "error: no standalone examples found" >&2
  exit 1
fi

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/verify-all.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

succeeded=()
failed=()

printf 'Found %d standalone examples. Running make target: %s\n\n' "${#examples[@]}" "$target"

for example in "${examples[@]}"; do
  log_file="$tmp_dir/${example//\//__}.log"
  start_seconds=$SECONDS

  printf '[RUN ] %s\n' "$example"

  if [[ $verbose -eq 1 ]]; then
    make -C "$example" "$target"
    status=$?
  else
    make -C "$example" "$target" >"$log_file" 2>&1
    status=$?
  fi

  elapsed=$((SECONDS - start_seconds))

  if [[ $status -eq 0 ]]; then
    succeeded+=("$example")
    printf '[ OK ] %s (%ss)\n\n' "$example" "$elapsed"
  else
    failed+=("$example")
    printf '[FAIL] %s (exit %d, %ss)\n' "$example" "$status" "$elapsed"
    if [[ $verbose -eq 0 ]]; then
      sed 's/^/       /' "$log_file"
    fi
    printf '\n'

    if [[ $fail_fast -eq 1 ]]; then
      break
    fi
  fi
done

printf 'Summary: %d succeeded, %d failed, %d total\n' \
  "${#succeeded[@]}" "${#failed[@]}" "$((${#succeeded[@]} + ${#failed[@]}))"

if [[ ${#succeeded[@]} -gt 0 ]]; then
  printf '\nSucceeded:\n'
  printf '  %s\n' "${succeeded[@]}"
fi

if [[ ${#failed[@]} -gt 0 ]]; then
  printf '\nFailed:\n'
  printf '  %s\n' "${failed[@]}"
  exit 1
fi

exit 0
