# Hostile audit: high prime-power gap component

## Outcome

**The high-component theorem is a mathematical PASS as a self-contained paper
proof.  Its Lean status is OPEN.**

The Nair-Shorey short-gap strip is **EXTERNAL/PAPER-ONLY** and is not included
in that PASS verdict.  Its quoted greatest-prime-factor theorem has neither
been imported into Lean nor independently proved here.

The result does not solve Erdős 686.  It removes exactly those gaps having a
prime-power component that meets one displayed dominance inequality.  Gaps
whose every primary component is smaller remain.

## Per-node dependency verdict

| Node | Verdict | Audit reason |
|---|---|---|
| Product ratio identity | PASS | Division is by a positive product of positive natural terms. |
| `3n>d` | PASS | If not, every factor is at least `7/4`; `k>=16` is stronger than the three factors needed. |
| `18(n+1)<13kd` | PASS | Exact binomial majorant is `4-267/103259`; no decimal exponential estimate. |
| At most one `p^e` owner | PASS | The `k` lower terms have diameter `k-1<q`.  Equality `q=k` is safe. |
| Translation for valuations `<e` | PASS | Factoring `p^s` leaves a unit plus `p^(e-s)m`; unit congruence is modulo exactly `p^(e-s)`. |
| Translation for valuations `>e` | PASS | `p^s u+p^e m=p^e(p^(s-e)u+m)` and the parenthesis is a unit. |
| `p>=5`, `s<e` | PASS | `U'=U (mod p)` conflicts with `U'=4U`; `3U` is a unit multiple of 3. |
| `p>=5`, `s=e` | PASS | Unique owner; all nonowner valuations are at most `lambda_p(k)`; exact divisor is `p^(e-lambda)`. |
| `p>=5`, `s>e` | PASS | One valuation falls and none rises, conflicting with equal total `p`-valuation. |
| `p=2`, `s<e` | PASS | Translation preserves total valuation, but multiplier 4 requires an increase by exactly two. |
| `p=2`, `s=e` | PASS | Owner supplies the entire increase, so `v_2(a+m)=2`; division by four is explicit. |
| `p=2`, `s>e` | PASS | Total valuation strictly falls, so it cannot rise by two. |
| `p=3`, `s<=e-2` | PASS | All normalized units are fixed modulo 9, where `U'=4U` is impossible for a unit. |
| `p=3`, `s=e` | PASS | Owner equation modulo 3 implies `m=0 (mod 3)`, contradicting exactness of `p^e || d`. |
| `p=3`, `s=e-1`, owner count | PASS | At least one owner exists; three `3^(e-1)` multiples would contain a `3^e` multiple; hence one or two. |
| `p=3`, two half-owners | PASS | The two normalized units are the two nonzero mod-3 classes; exhaustive mod-9 check gives zero solutions. |
| `p=3`, singleton lift | PASS | Nonowner loss is exactly `mu=min(lambda_3(k),e-2)`; division of the mod-`3^(e-mu)` congruence by 3 is legal because `e-mu>=2`. |
| Positive residual quantities | PASS | They are `3a-m` for `p!=3` and `a-m` for `p=3`, positive directly from `3n>d`. |
| Upper residual quantities | PASS | Both are strictly below `R_k(d)/(6q)` by the displayed `18(n+i)` bound. |
| Strict/non-strict boundary | PASS | HC uses `R<=threshold`; the candidate multiple is strictly smaller than the modulus, so equality at the HC boundary is excluded. |
| Simple conditions | PASS | Exact bound `R<15kd`; exact component-size constants checked for all three prime classes. |
| `d=p^(k+t)` family | PASS | Base cases plus monotone induction inequalities prove all exponents, not merely the finite verifier sweep. |
| Nair-Shorey strip | EXTERNAL | Only surrounding arithmetic is reproduced; the greatest-prime-factor input is paper-only. |
| Lean formalization | OPEN | No theorem declaration, axiom printout, or kernel attestation exists for this result. |

## No hidden uniformity

Every qualitative phrase in the source proof reduces to one of these exact
bounds:

```text
nonowner valuation:          v_p(n+j) <= lambda_p(k)
p=3 nonowner valuation:      v_3(n+j) <= min(lambda_3(k),e-2)
p>=5 owner divisor:          p^(e-lambda_p(k))
p=2 owner divisor:           2^(e-lambda_2(k)+2)
p=3 owner divisor:           3^(e-mu_3(k,e)-1)
p!=3 positive size:          0 < 3a-m < R_k(d)/(6p^e)
p=3 positive size:           0 < a-m  < R_k(d)/(6p^e).
```

The theorem does not require a terminating row search, a finite-field cover,
an owner-supply conjecture, or a bound with an unspecified constant.

## Modular branch census

The verifier encodes the full top-level partitions:

| Prime class | Exhaustive values of `s=max v_p(n+i)` |
|---|---|
| `p>=5` | `s<e`, `s=e`, `s>e` |
| `p=2` | `s<e`, `s=e`, `s>e` |
| `p=3` | `s<=e-2`, `s=e-1`, `s=e`, `s>e` |

It then enumerates all residue classes in each nontrivial modular reduction.
The most fragile branch, `p=3` and `s=e-1`, has exact census

```text
one owner:  36 admissible (a,m) tuples modulo 9, 18 solutions;
two owners: 108 admissible (a1,a2,m) tuples modulo 9, 0 solutions.
```

The two-owner enumeration includes precisely the tuples with `a1` and `a2`
in distinct nonzero classes modulo 3.  The singleton solutions then satisfy
`m=a (mod 3)` as claimed and lift exactly to
`3^(L-1)|(a-m)` modulo `3^L`.

For `p=2`, all odd `(a,m)` pairs modulo `2^(L+2)` are enumerated for
`1<=L<=6`, and only those with `v_2(a+m)=2` are retained.  For every retained
pair,

```text
(a+m)/4 = a (mod 2^L)
iff
2^(L+2) | (3a-m).
```

For `p>=5`, every unit product modulo each prime through `47` is checked in
the low branch; the owner lift is exhausted modulo `p^L` for
`p in {5,7,11}`, `L in {1,2}`.  The residue identity is algebraic for all
prime powers, while these finite sweeps guard implementation and sign errors.

## Boundary audit

- `k=16`: included.  All archimedean and simple-condition inequalities are
  strict at or before this boundary.
- Odd `k`: the high-component theorem itself does not use evenness.  The
  overall portfolio target may later specialize it to even rows.
- `q=k`: included.  A block of `k` terms has diameter `k-1`, so it still has
  at most one `q`-multiple.
- `p=2`: included separately; treating it as an odd prime would miss the
  multiplier valuation `v_2(4)=2`.
- `p=3`: included separately; the mod-`p` unit contradiction degenerates and
  the required repair is genuinely modulo 9.
- `e=1`: allowed for `p=2` or `p>=5` whenever `p^e>=k`; all exponent
  differences remain nonnegative because then `e>=lambda_p(k)+1`.
- `p=3` small exponent: `q>=k>=16` forces `e>=3`, so `mu_3(k,e)` is defined
  and `e-mu>=2`.
- Composite cofactor `m`: unrestricted except for `p` not dividing `m`.
  Extra prime factors are allowed.
- Equality in HC: correctly excluded, because the equation yields a strict
  upper bound on a positive multiple of the modulus.
- Failure of HC: theorem is silent.  It does not say a small component permits
  a solution.
- `d=p^(k+t)`: includes `t=0`, every prime, and every natural `n`.

## Falsification-record audit

- The fixed-prefix witness `(984,3177026,4480)` is irrelevant: no prefix
  implication or local continuation assertion is used.
- The smooth-block census does not attack the proof: the hypothesis is a
  quantified component-dominance inequality, not smoothness alone.
- Failed finite-field intersections are irrelevant: the theorem uses exact
  valuations and an archimedean size contradiction, not a union of local
  masks.
- No unrestricted statement that an interior lower term is a prime power is
  made.  The prime power is a component of `d`, not a classification of a
  lower term.
- No row-specific cover is called an induction.  The proof is uniform in
  arbitrary `k>=16`.
- No owner-supply lemma is assumed.  The maximum-valuation split constructs
  the owner forced by the equation.

## Exact reproduction status

Commands:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_t2_high_component/high_component_verify.py

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t2_high_component/test_high_component_verify.py
```

Result: `7 passed in 0.20s`.

Exact sweeps:

```text
full components tested:                    98,172
simple-condition antecedents checked:      35,087
prime-power-family tuples checked:         13,875
ordinary external-strip arithmetic pairs: 113,074
k=82 external-strip arithmetic pairs:         200
```

The last two rows reproduce arithmetic only and must not be cited as evidence
for the external greatest-prime-factor theorem.

Frozen SHA-256 values:

```text
GPT-Pro attachment: 2262670ee74a62fb537493672abea66322eb6f79f0827d531814e2c96d220df6
exact verifier:      9351e898bf968ce53cf0a0df58ac63bb777cd347787d4ee4ddb936ef99574b9a
focused tests:       f5e94beb554484ed8776e02b2a694baf67a116be328d32dfc813028e554a8e8b
JSON audit payload:  dcd0557aaa23dd460dfcfb8f01ee7062619c3b0094df3ade5adbb2e495c6775a
```
