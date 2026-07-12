# Hostile audit: Target 2 three-owner quotient/lattice package

Verdict: **PASS as a proper partial package; FAIL as Target 2 closure.**

## Dependency tree

1. `even_reflected_third_composition_component`
   - Assumes the raw modulus-square next lift, two exact step-three residual
     differences, `P*a=g*Q*R+3*x`, `S=g*P*Q*R`, and `gcd(P,3)=1`.
   - Proves one displayed modulus-square affine obstruction.
   - It does not derive the raw next lift or construct the three buckets.
2. `odd_reflected_third_composition_component`
   - Same dependency shape, with step five and `gcd(P,5)=1`.
3. `reflected_third_composition_lattice_identity`
   - Pure integer polynomial identity.  It eliminates the two named common
     variables and has no number-theoretic premise.
4. Exact verifier
   - Reproduces the 121-digit window counterfixture, 180 boundary/deep rows
     for the `k>=220` linear estimates, two square-lift dependency fixtures,
     and 185 canonical mixed sign cells for `16<=k<=200`.
   - None of these finite scans is used as a universal proof.

## Per-node verdicts

| Node | Verdict | Reason |
|---|---|---|
| Even composition | PASS | Kernel checked; conclusion is strictly weaker than Target 2 and retains every hypothesis. |
| Odd composition | PASS | Kernel checked; no division by five without explicit coprimality. |
| Lattice identity | PASS | Direct ring identity. |
| Uniform `k>=16` expected floor | FAIL | Exact `d=10^120`, `k=16` endpoint-window witness has products below 15 and 3. |
| Restricted `k>=220` floor | PASS as arithmetic derivation | It follows from the already-banked `k*d<5*n`; it does not itself contradict a solution. |
| Uniform one-sided lattice claim | FAIL | All 185 canonical exact cells from `k=16` through `200` are mixed. |
| Target 2 | OPEN | Small-prime loss and noncanonical at-least-three-owner cells remain. |

## Quantified bounds replacing informal language

- "Deep" means exactly `d=10^120` in the frozen `k=16` witness.
- "Restricted large k" means every natural `k,n,d,i` with
  `220<=k`, `k<=d`, `k*d<5*n`, and `1<=i<=k`.
- "Canonical scan" means exactly 185 rows `16<=k<=200`, with
  `d=10^6*k`, midpoint `n` of the exact endpoint-window band, and owners
  `(1,floor((k+1)/2),k)`.
- No claim is made for the other `C(k,3)-1` owner triples in a scanned row.

## Boundary/falsification record

- The deep window witness does not have the three square decompositions.  It
  falsifies only a deduction from the ratio window alone.
- `(16,8341,4500)` has all three even square decompositions but fails the
  endpoint window.
- `(16,8547105,847742)` has all three squares, satisfies `9d<n` and the lower
  endpoint window, but fails the upper endpoint window.
- No modular claim is inferred from either failed equation fixture.
- The package does not invoke smoothness alone, a fixed row-prefix cap, or a
  theorem-strength assertion that the center has only three components.

## Reproduction and frozen hashes

```text
db42a04129fc6da8089afca7b533af69555172f22ba63a0753af42ba61c4849f  ErdosProblems/Erdos686ReflectedThirdComposition.lean
5587373181bb976fd7eb167b4ced90161f9bda49d6cad33401a0ec059541e557  compute/campaign686/agent_t2_three_owner/three_owner_floor_lattice_verify.py
9d0ad48ffd050f4ac0b23dd16e8201ff28357f23add37b8caf541d6c5bf21acd  compute/campaign686/agent_t2_three_owner/test_three_owner_floor_lattice_verify.py
a7231c0ce46baa8aa3b5b6aa6ce1823b46270dff3c103d167193cd4deb3ee701  compute/campaign686/agent_t2_three_owner/findings.md
```

Commands and observed results:

```text
lake env lean ErdosProblems/Erdos686ReflectedThirdComposition.lean
  PASS; public surfaces use only propext, Classical.choice, Quot.sound

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q compute/campaign686/agent_t2_three_owner
  4 passed in 19.25s
```
