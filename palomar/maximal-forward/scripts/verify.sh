#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd "$(dirname "$0")/.." && pwd)
repository_root=$(git -C "$project_root" rev-parse --show-toplevel)
cd "$project_root"

for required in \
  lean-toolchain lakefile.toml lake-manifest.json formalization.yaml \
  Challenge.lean Solution.lean comparator.json; do
  test -f "$required" && test ! -L "$required" || {
    echo "error: missing or symbolic-link Palomar file: $required" >&2
    exit 1
  }
done

test -f "$repository_root/LICENSE" && test ! -L "$repository_root/LICENSE" || {
  echo "error: repository-root LICENSE is missing or symbolic" >&2
  exit 1
}

challenge_sorries=$(grep -Ec '^  sorry$' Challenge.lean || true)
test "$challenge_sorries" -eq 1 || {
  echo "error: expected one deliberate Challenge sorry, found $challenge_sorries" >&2
  exit 1
}

if grep -ERn '\b(sorry|admit|sorryAx)\b|^[[:space:]]*(axiom|unsafe)\b' \
    Solution.lean PalomarMaximalForward; then
  echo "error: proof-bearing source contains a placeholder, axiom, or unsafe declaration" >&2
  exit 1
fi

ruby scripts/validate-formalization.rb formalization.yaml

lake build
lake env lean Challenge.lean
lake env lean Solution.lean

while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *)
      echo "error: Challenge import closure is not Lean-core/Mathlib-only: $dependency" >&2
      exit 1
      ;;
  esac
done < <(lake env lean --src-deps Challenge.lean)

axioms=$(lake env lean /dev/stdin <<'EOF'
import Solution
#print axioms DifferentialGeometry.Palomar.Submission.exists_finite_or_immortal_envelope
EOF
)
for expected in propext Classical.choice Quot.sound; do
  grep -Fq "$expected" <<<"$axioms" || {
    echo "error: expected axiom not reported: $expected" >&2
    exit 1
  }
done

if grep -Eq 'sorryAx|Lean\.ofReduceBool' <<<"$axioms"; then
  echo "error: forbidden axiom reported" >&2
  exit 1
fi

if [ "$(uname -s)" = "Darwin" ]; then
  PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 ./scripts/verify-comparator.sh
else
  ./scripts/verify-comparator.sh
fi

git -C "$repository_root" diff --check
echo "Maximal-forward Palomar checks passed."
