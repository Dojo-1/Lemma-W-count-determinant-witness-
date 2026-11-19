#!/usr/bin/env bash
set -euo pipefail

# Hardened verification suite for the Lemma W / Octonion Bracketing formalization.
#
# Runs:
#   1. Static source hygiene & TCB import isolation checks (Spec.lean, Challenge.lean, Solution.lean, Caterpillar/)
#   2. Warning-free `lake build` of all default targets (Spec, Caterpillar, Solution)
#   3. Whole-project `lake check` (sandboxed export + replay of all default targets; pass `--full-check` for `--paranoid` across all 62k Init decls)
#   4. `lake comparator --paranoid` against `comparator.json` (Challenge vs. Solution, all 6 kernels: lean, leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron)
#   5. Adversarial negative controls (verifies `lake comparator` rejects forbidden axioms and statement mismatches)
#   6. Exact `#print axioms` allowlist audit on all headline theorems
#
# Usage:
#   ./scripts/verify_hardened.sh                  # Full bwrap sandbox (default, required in CI)
#   ./scripts/verify_hardened.sh --no-sandbox     # For containers without bwrap / user namespaces
#   ./scripts/verify_hardened.sh --full-check     # Also pass --paranoid to Gate 3 whole-project `lake check`

NO_SANDBOX=0
FULL_CHECK=0
for arg in "$@"; do
  case "$arg" in
    --no-sandbox) NO_SANDBOX=1 ;;
    --full-check) FULL_CHECK=1 ;;
    *) echo "Unknown argument: $arg" >&2; exit 2 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$LEAN_DIR"

SANDBOX_ARGS=()
if [ "$NO_SANDBOX" -eq 1 ]; then
  echo "WARNING: Running with --inadvisably-no-sandbox (container fallback; CI uses full bwrap sandbox)."
  SANDBOX_ARGS+=(--inadvisably-no-sandbox)
fi

echo "=== [1/6] Static source hygiene & TCB isolation ==="

python3 - <<'PY'
import pathlib, re, sys

def strip_lean_comments(src: str) -> str:
    out = []
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        if in_str:
            c = src[i]
            out.append(c)
            if c == '\\' and i + 1 < n:
                out.append(src[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
        elif depth > 0:
            if src[i:i+2] == '/-':
                depth += 1
                i += 2
            elif src[i:i+2] == '-/':
                depth -= 1
                i += 2
            elif src[i] == '\n':
                out.append('\n')
                i += 1
            else:
                i += 1
        else:
            if src[i:i+2] == '--':
                while i < n and src[i] != '\n':
                    i += 1
            elif src[i:i+2] == '/-':
                depth += 1
                i += 2
            elif src[i] == '"':
                in_str = True
                out.append('"')
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)

def check_no_match(path: pathlib.Path, pattern: re.Pattern, desc: str) -> None:
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    for lineno, line in enumerate(code.splitlines(), 1):
        m = pattern.search(line)
        if m:
            print(f"FAIL ({desc}): {path}:{lineno}: matched {m.group(0)!r}: {line.strip()}", file=sys.stderr)
            sys.exit(1)

# 1a. Spec.lean must have zero imports and pure definitions only (no proofs/axioms/escape hatches)
spec_path = pathlib.Path("Spec.lean")
check_no_match(spec_path, re.compile(r"^\s*import\b"), "Spec.lean must have zero imports")
check_no_match(
    spec_path,
    re.compile(r"\b(sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|theorem|lemma|by)\b"),
    "Spec.lean must contain pure definitions only",
)

# 1b. Challenge.lean must import ONLY Spec
chal_code = strip_lean_comments(pathlib.Path("Challenge.lean").read_text(encoding="utf-8"))
chal_imports = [l.strip() for l in chal_code.splitlines() if re.match(r"^\s*import\b", l)]
if chal_imports != ["import Spec"]:
    print(f"FAIL: Challenge.lean must import ONLY 'Spec'; found: {chal_imports}", file=sys.stderr)
    sys.exit(1)

# 1c. Solution.lean, Caterpillar.lean, Caterpillar/, Spec.lean must have zero forbidden escape hatches
forbidden = re.compile(
    r"\b(sorry|admit|axiom|unsafe|native_decide|trustCompiler|ofReduceBool|ofReduceNat|skipKernelTC)\b"
    r"|implemented_by|@\[extern|decide\s*\+native|^\s*partial\s+def\b"
)
files = [spec_path, pathlib.Path("Solution.lean"), pathlib.Path("Caterpillar.lean")]
files += sorted(pathlib.Path("Caterpillar").rglob("*.lean"))
for f in files:
    check_no_match(f, forbidden, "forbidden escape hatch")

print(f"PASS: Source hygiene & TCB isolation checks passed ({len(files)} files audited).")
PY

echo "=== [2/6] Clean build of default targets (Spec, Caterpillar, Solution) ==="
BUILD_LOG="$(mktemp)"
trap 'rm -f "$BUILD_LOG"' EXIT
lake build 2>&1 | tee "$BUILD_LOG"
if grep -qE '^warning:' "$BUILD_LOG"; then
  echo "FAIL: Build produced warnings." >&2
  exit 1
fi
echo "PASS: Default targets built with 0 errors and 0 warnings."

if [ "$FULL_CHECK" -eq 1 ]; then
  echo "=== [3/6] Whole-project 6-kernel verification: lake check --paranoid ==="
  lake check --paranoid "${SANDBOX_ARGS[@]}"
  echo "PASS: lake check --paranoid accepted by all bundled kernels."
else
  echo "=== [3/6] Whole-project export & kernel verification: lake check ==="
  lake check "${SANDBOX_ARGS[@]}"
  echo "PASS: lake check accepted all default targets (Spec, Caterpillar, Solution)."
fi

echo "=== [4/6] Multi-kernel Challenge/Solution verification: lake comparator --paranoid ==="
lake comparator --paranoid "${SANDBOX_ARGS[@]}" --config comparator.json
echo "PASS: lake comparator --paranoid accepted by all 6 bundled kernels."

echo "=== [5/6] Adversarial negative controls ==="
NEG_DIR="$(mktemp -d)"
trap 'rm -rf "$BUILD_LOG" "$NEG_DIR"' EXIT
cp lean-toolchain "$NEG_DIR/"
cat > "$NEG_DIR/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package «negtest» where
lean_lib «NegChallenge» where
lean_lib «NegSolAxiom» where
lean_lib «NegSolMismatch» where
EOF
cat > "$NEG_DIR/NegChallenge.lean" <<'EOF'
theorem target : 2 + 2 = 4 := by sorry
EOF
cat > "$NEG_DIR/NegSolAxiom.lean" <<'EOF'
axiom cheat : False
theorem target : 2 + 2 = 4 := False.elim cheat
EOF
cat > "$NEG_DIR/NegSolMismatch.lean" <<'EOF'
theorem target : 2 + 2 = 5 → 2 + 2 = 4 := fun _ => rfl
EOF
cat > "$NEG_DIR/neg_axiom.json" <<'EOF'
{
  "challenge_module": "NegChallenge",
  "solution_module": "NegSolAxiom",
  "theorem_names": ["target"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
cat > "$NEG_DIR/neg_mismatch.json" <<'EOF'
{
  "challenge_module": "NegChallenge",
  "solution_module": "NegSolMismatch",
  "theorem_names": ["target"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
(
  cd "$NEG_DIR"
  lake update >/dev/null 2>&1 || true
  if [ ! -f lake-manifest.json ]; then
    cat > lake-manifest.json <<'EOF'
{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "name": "negtest", "lakeDir": ".lake"}
EOF
  fi
  set +e
  lake comparator "${SANDBOX_ARGS[@]}" --config neg_axiom.json >/dev/null 2>&1
  RC_AXIOM=$?
  lake comparator "${SANDBOX_ARGS[@]}" --config neg_mismatch.json >/dev/null 2>&1
  RC_MISMATCH=$?
  set -e
  if [ "$RC_AXIOM" -ne 1 ]; then
    echo "FAIL: Negative control (forbidden axiom) expected exit code 1, got $RC_AXIOM" >&2
    exit 1
  fi
  if [ "$RC_MISMATCH" -ne 1 ]; then
    echo "FAIL: Negative control (statement mismatch) expected exit code 1, got $RC_MISMATCH" >&2
    exit 1
  fi
)
echo "PASS: Comparator rejected both forbidden-axiom (rc=1) and statement-mismatch (rc=1) controls."

echo "=== [6/6] Exact #print axioms allowlist audit ==="
AXIOM_FILE="$(mktemp --suffix=.lean)"
trap 'rm -rf "$BUILD_LOG" "$NEG_DIR" "$AXIOM_FILE"' EXIT
cat > "$AXIOM_FILE" <<'EOF'
import Solution
#print axioms Challenge.main
#print axioms Challenge.count_disconnected
#print axioms Challenge.canonical
#print axioms Challenge.rgs_nodup
#print axioms Challenge.kerconn_rename
#print axioms Challenge.stirling_rec
#print axioms Challenge.bell_eq_sum
#print axioms Challenge.lemmaW_exists
#print axioms Challenge.kerflip_dn
#print axioms Challenge.octonion_unital
#print axioms Challenge.octonion_norm_mul
#print axioms Challenge.octonion_non_associative
#print axioms Challenge.octonion_moufang
#print axioms Challenge.kerconn_two_letters_example
#print axioms Challenge.kerconn_interval_example
#print axioms Challenge.not_kerconn_example
#print axioms Challenge.bell_small_values
#print axioms Challenge.disconnected_count_four_five
#print axioms MainThm.main
#print axioms Count.count_disconnected
#print axioms Canon.canonical
#print axioms Canon.rgs_nodup
#print axioms Canon.kerconn_rename
#print axioms Canon.stirling_rec
#print axioms Canon.bell_eq_sum
#print axioms WExist.lemmaW_exists
#print axioms WExist.kerflip_dn
EOF
AXIOM_OUT="$(lake env lean "$AXIOM_FILE")"
echo "$AXIOM_OUT"
python3 - "$AXIOM_OUT" <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = [l.strip() for l in sys.argv[1].splitlines() if l.strip()]
assert len(lines) == 27, f"Expected 27 axiom lines, got {len(lines)}"
for line in lines:
    if "does not depend on any axioms" in line:
        continue
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    assert m, f"Unexpected #print axioms output: {line}"
    used = {a.strip() for a in m.group(1).split(",") if a.strip()}
    bad = used - allowed
    assert not bad, f"Disallowed axioms {bad} in: {line}"
print("PASS: All 27 audited declarations depend only on subsets of {propext, Classical.choice, Quot.sound}.")
PY

echo "=== ALL HARDENED VERIFICATION GATES PASSED ==="
