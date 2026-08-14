#!/usr/bin/env bash
# Run inside a fresh clone. This proves the selected proof without Math,
# authority credentials, a hosted Vela service, or an inherited project cache.
set -euo pipefail

fail() { echo "FAIL: $*" >&2; exit 1; }

[ -f vela.toml ] || fail "run from the lean-proofs repository root"
[ ! -e .lake ] || fail "cold consumer requires a checkout with no inherited .lake"
[ ! -e .vela/repository.json ] || fail "native integration must not contain authority state"
[ ! -e .vela/authority ] || fail "native integration must not contain authority keys"

unset SSH_AUTH_SOCK GITHUB_TOKEN GH_TOKEN || true

output="${1:-erdos-154-verification-input.json}"
repeat_output="$(mktemp -t lean-proofs-erdos154.XXXXXX)"
trap 'rm -f "$repeat_output"' EXIT

python3 scripts/check_vela_integration.py
lake exe cache get
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
python3 scripts/check_vela_integration.py --emit "$output"
python3 scripts/check_vela_integration.py --emit "$repeat_output"
cmp "$output" "$repeat_output"

echo "PASS: cold-consumed Erdős 154 without Math, authority credentials, or hosted Vela"
echo "portable output: $output"
