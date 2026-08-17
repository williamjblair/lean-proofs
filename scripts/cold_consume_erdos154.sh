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

vela_bin="${VELA_BIN:-vela}"
command -v "$vela_bin" >/dev/null 2>&1 || fail "Vela Core CLI is required for the shared integration waist"
[ "$("$vela_bin" --version)" = "vela 0.976.1" ] || fail "Vela Core CLI version must be 0.976.1 from signed release commit 329487f29ad4c6313a2be7c091d46085b61ff03b"

output="${1:-erdos-154-verification-input.json}"
consumer_state="$(mktemp -d -t lean-proofs-erdos154.XXXXXX)"
repeat_output="$consumer_state/repeat-output.json"
export XDG_CACHE_HOME="$consumer_state/cache"
trap 'rm -rf -- "$consumer_state"' EXIT

"$vela_bin" integration check . --json
python3 scripts/check_vela_integration.py --vela-bin "$vela_bin"
lake exe cache get
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
python3 scripts/check_vela_integration.py --vela-bin "$vela_bin" --emit "$output"
python3 scripts/check_vela_integration.py --vela-bin "$vela_bin" --emit "$repeat_output"
cmp "$output" "$repeat_output"

echo "PASS: cold-consumed Erdős 154 without Math, authority credentials, or hosted Vela"
echo "portable output: $output"
