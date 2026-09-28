#!/usr/bin/env bash
# Run from any directory. Pass --fetch-cache on a fresh checkout to download
# the pinned Mathlib binary cache before checking the Section 4 additions.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
report_dir="${SECTION4_REPORT_DIR:-$repo_root/registry/section4/verification}"
mkdir -p "$report_dir"
cd "$repo_root/GenLimitLean"
case "${1:-}" in
  --fetch-cache) lake exe cache get ;;
  "") ;;
  *) echo "Usage: $0 [--fetch-cache]" >&2; exit 2 ;;
esac
{
  date -u '+Checked at %Y-%m-%dT%H:%M:%SZ'
  lean --version
  lake --version
  printf '%s\n' 'Source-control history intentionally omitted from the anonymous release module.'
  shasum -a 256 lean-toolchain lakefile.toml lake-manifest.json Section4.lean
  find Section4 -name '*.lean' -type f -exec shasum -a 256 {} \; | sort
} > "$report_dir/environment-and-sources.txt"
python3 ../scripts/audit_section4.py scan "$report_dir/static-scan.log"
lake build Section4 2>&1 | tee "$report_dir/build.log"
lake env lean ../scripts/section4_axioms.lean 2>&1 | tee "$report_dir/axioms.log"
python3 ../scripts/audit_section4.py axioms "$report_dir/axioms.log" "$report_dir/axiom-check.log"
{
  printf '%s\n' '# Verification status for this snapshot'
  printf '\n'
  printf '%s\n' 'The focused `lake build Section4` and endpoint axiom audit completed successfully.'
  printf '%s\n' 'See the adjacent logs for the compiler output and declared logical dependencies.'
  printf '%s\n' 'A repository-wide `lake build` is separate from this Section 4 verification script.'
} > "$report_dir/STATUS.md"
printf '%s\n' 'Section 4 compilation and axiom audit completed.'
