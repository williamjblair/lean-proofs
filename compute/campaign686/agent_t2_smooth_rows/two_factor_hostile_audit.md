# Hostile audit: two-large-factor reflection center

Verdict: **PASS as a strict equation-level exclusion of the one/two reflected-
owner no-small-prime center branch, plus an explicit bound on every small-
base component.  FAIL as a complete Target 2 closure.**

## Exact theorem audited

Under `k>=16`, `d>=k`, primes `p,r>k` dividing
`S=2n+d+k+1`, and the exact factorization

```text
S = p^v_p(S) * r^v_r(S),
```

the equation `B(k,n+d)=4B(k,n)` is impossible.

More strongly, `q` and `r` may be arbitrary aggregates whose prime supports
are entirely above `k`, provided each aggregate occupies one reflected owner.
The one-aggregate case is impossible as well.

## Dependency tree

```text
exact block-product equation
|
+- banked 9d<n inequality
|
+- complete large-prime reflected square lift, once for p and once for r
|  +- full center valuation survives for each base >k
|  `- reflected owner linear form is divisible by the component square
|
+- exact center factorization S=q*r
|
`- parity split
   +- even k
   |  +- 5S^2 < L_i*L_j < 8S^2, hence uv in {6,7}
   |  +- uv=6 excluded modulo 3
   |  `- uv=7 excluded by 5r<2q and 2q<5r (or symmetrically)
   `- odd k
      +- S^2 < M_i*M_j < 4S^2, hence uv in {2,3}
      `- both values excluded by nonzero squares modulo 5
```

No node assumes `LargeKSmoothHypothesis`, a dominant prime power, or a
finite row prefix.

## Per-node verdicts

| Node | Verdict | Exact evidence |
|---|---|---|
| Reflected square lift for each complete component | PASS | Imported kernel theorem; both natural-number parity forms are derived without loss. |
| Even product window | PASS | Universal Lean inequalities; 27,252 producer and 14,616 independent exact sampled rows. |
| Even `uv=6` residue obstruction | PASS | Complete nonzero-square table modulo 3. |
| Even `uv=7` size obstruction | PASS | Both opposing strict inequalities proved in Lean from closed identities. |
| Odd product window | PASS | Universal Lean inequalities, covered by both exact grids. |
| Odd `uv in {2,3}` residue obstruction | PASS | All 16 nonzero residue pairs modulo 5, both orientations and both multipliers. |
| Equation-level specialization | PASS | Exact factorization exponents and both owner lifts are constructed in Lean. |
| Composite owner aggregation | PASS | Large-support coprimality cancels the local factorial weight for arbitrary `q,r`. |
| One-owner boundary | PASS | `S^2<=7n` contradicts `S>2n` and `n>9d`; explicit Lean theorem. |
| Small-prime residual alternative | PASS | Residual is at most `k-1`, or its weighted reflected square is at most `(k-1)!*7n`. |
| Full small-prime power bound | PASS | Exact restored loss is `p^(2 ell_p)*((k-1)^2+(k-1)!*7n)`. |
| Reflected next-order signs | PASS exact arithmetic; **Lean pending** | 66,910 exact rows give `-12D_i x^2` for even and `+20D_i x^2` for odd. |
| Dropping a global loss `g` | **REFUTED AS AN INFERENCE** | For `S=gqr`, multiplier windows scale by `g^2`; the `g=1` finite cases no longer apply. |
| Mandatory fixtures | PASS | Both remain non-equations; exact center factorizations reproduced. |
| Mixed small-prime center | **OPEN** | The explicit per-prime loss bounds do not yet control their aggregate product. |
| Three-or-more large owners | **OPEN** | One/two owner aggregation is closed; the joint three-owner CRT/window problem remains. |
| `LargeKSmoothHypothesis` | **OPEN** | The two open branches above remain. |

The producer searched 26,136 target-range centers, plus 9,348 centers through
the large-supported owner-aggregate filter.  The independent implementation
searched 15,456 centers and examined 801 oriented factor pairs with both
factors above `k` and suitable residue units; 108 pairs had fully large
prime support, and none had both square lifts.  It also checked 2,680
one-component centers.  These are falsification checks only.  Universality
comes from the Lean proof.

## Boundary audit

- `(984,3177026,4480)` passes rows `1..16`, fails row 17, and is not the
  exact equation.  Its center is `3^2*706613`, so it also contains a small
  prime component and does not satisfy the headline two-large-factor premise.
- `(244,48502,277)` passes rows `1..15`, fails row 16, and is not the exact
  equation.  Its center is `2*11^2*13*31`; it has no prime base above `k`.
- The theorem never promotes either row-prefix survivor to an equation-level
  reflected square lift.

## Exact remaining quantified branch

For a hypothetical solution, every complete component `p^v_p(S)` with
`p>k` obeys

```text
(p^v_p(S))^2 <= 7n.
```

For every small base the exact alternatives (3)--(4) in `findings.md` apply.
In addition, `S` must have a prime divisor at most `k`, or its large
components must occupy at least three distinct reflected owners.  Excluding
precisely that disjunction is still required for Target 2.

## Reproduction

```bash
python3 -m pytest -q compute/campaign686/agent_t2_smooth_rows
python3 compute/campaign686/agent_t2_smooth_rows/two_factor_center_hostile_verify.py
lake env lean ErdosProblems/Erdos686ReflectedAlignmentTwoFactor.lean
```

The Lean axiom output for every displayed public theorem is exactly
`[propext, Classical.choice, Quot.sound]`.

## Frozen source hashes

```text
9bab7a6b123512db3af5b27dedef2cb46cc844091148232e80aa3d73c8d24039  ErdosProblems/Erdos686ReflectedAlignmentTwoFactor.lean
9de72920ff5ac9d37edb3caec644df327fe651f6043b5744336e7f1f13e02ec4  compute/campaign686/agent_t2_smooth_rows/two_factor_center.py
8e460010e9e9a6b7c63eaab682b6bf3cd6206040d87ffb32927c820117881eb5  compute/campaign686/agent_t2_smooth_rows/test_two_factor_center.py
ede4fe47fdf76ae57db07e15cf35ac3fc29e635bb30381bcd7c4e2cfca1c7c4b  compute/campaign686/agent_t2_smooth_rows/two_factor_center_hostile_verify.py
831db6f77eb57f990d4066b66242d903e775bbe40f0b99980d78cced0269f290  compute/campaign686/agent_t2_smooth_rows/test_two_factor_center_hostile_verify.py
452f2fdf2d140fa02a3420f0a7b41778efbbcdf682ef36952c65b6a60920d3cd  compute/campaign686/agent_t2_smooth_rows/reflected_second_lift.py
aa5f8e88010f3d0cdd64df4158ae495af2a7d6da41c524e28359e6f80f7d084e  compute/campaign686/agent_t2_smooth_rows/test_reflected_second_lift.py
```

Hashes record the pre-report source snapshot.  Regenerate them after any
source edit and update this table before integration.
