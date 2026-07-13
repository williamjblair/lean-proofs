# Hostile audit: tail-1000 center/reflected three-bucket packing

## Verdict

**PASS for the exact numerical cutoff and generic packing corollary.  PASS
for the equation-facing theorem only on a supplied exact center/reflected
three-bucket decomposition.  FAIL as a proof of the arbitrary-owner odd tail,
`OddThueTail1000Hypothesis`, Target 1, or Erdős #686.**

The upgrade is not a new congruence obstruction.  The determinant and local
lifts were already banked.  The new fact is the exact inequality

```text
HC(k)^2 * KD(k,r)^3 * G_k^12 < 10^200 < 10^1000
```

for all 27 target center/reflected pairs, plus its composition with the
equation-derived center and endpoint bounds in the supplied slice.

## Dependency tree with exact statements

```text
N0  supplied target geometry
    k in {5,7,9,11,13,15}
    1 <= r < (k+1)/2
    m=(k+1)/2, i=m-r, l=m+r
 |
 +-- N1  exact equation and tail
 |       blockProduct k (n+d) = 4*blockProduct k n
 |       10^1000 <= d
 |    |
 |    +-- N2  equation windows
 |    |       R_k*d < H_k*localResidual n d m
 |    |       localResidual n d m < U_k*d
 |    |
 |    `-- N3  supplied exact decomposition
 |            0<g,P,Q,R
 |            d=g*P*Q*R
 |            g<=G_k
 |            P|n+m, Q|n+i, R|n+l
 |            X=a*P^2
 |            X-3r=b*Q^2
 |            X+3r=c*R^2
 |         |
 |         +-- N4  center raw cubic
 |         |       P^3 < HC(k)*d
 |         |
 |         +-- N5  endpoint third lifts
 |         |       Q^2 | T_-
 |         |       R^2 | T_+
 |         |
 |         `-- N6  exact product identity
 |                 (abc)*d^2=g^2*X*(X^2-9r^2)
 |
 +-- N7  determinant
 |       Delta=(X-3r)T_+-(X+3r)T_-
 |            =54r(Cabc-8DXg^2r-40Eg^2r^2d)
 |       Q^2*R^2 | Delta
 |    |
 |    +-- N8  determinant nonzero from N2 and N6
 |    |       Cabc-8DXg^2r-40Eg^2r^2d != 0
 |    |
 |    `-- N9  exact absolute bound
 |            Q^2*R^2 < KD(k,r)*g^2*d
 |
 +-- N10 finite cutoff, every target pair
 |        HC(k)^2*KD(k,r)^3*G_k^12 < 10^200 < 10^1000
 |
 `-- N11 packing
          d < HC(k)^2*KD(k,r)^3*g^12
            <= HC(k)^2*KD(k,r)^3*G_k^12
            < 10^1000 <= d
          contradiction
```

Here the exact constants are

```text
U_k = (14,17,23,26,29,35),
G_k = (108,1620,136080,1224720,242494560,18914575680),
HC(k) = (((k-1)/2)!)^2*U_k,
KD(k,r) = 54r(|C|U_k^3+8|D|U_k*r+40|E|r^2),
```

and

```text
(R_k,H_k) =
  (268048,31951), (278097,21902), (283346,16653),
  (286567,13432), (288745,11254), (290316,9683).
```

There is no phrase “sufficiently large,” “uniformly bounded,” or
“essentially the determinant.”

## Per-node verdict

| node | verdict | exact evidence |
|---|---|---|
| N0 | PASS | The finite range is exactly six odd rows and `1<=r<(k+1)/2`, giving `2+3+4+5+6+7=27` unordered pairs. |
| N1 | PASS | The tail premise is the closed inequality `10^1000<=d`; equality is included. |
| N2 | PASS | `target_exactRatio_localResidual_lower` supplies the exact rational lower bound; the row ratio-window lemmas supply `X<U_k*d`.  No decimal root estimate occurs. |
| N3 | SUPPLIED, NOT DERIVED | This is the scope boundary.  The theorem does not derive an exhaustive three-component factorization or this owner geometry from an arbitrary equation. |
| N4 | PASS | `center_raw_cube_lt_factorial_sq_mul` yields `P^3<HC(k)d` from the equation, `P|d`, and `P|n+m`. |
| N5 | PASS at the algebraic layer | `third_order_local_lift` and `three_bucket_third_obstruction_dvd_sq` give the two displayed endpoint divisibilities after the reflected coefficient identities. |
| N6 | PASS | `reflected_three_bucket_product_identity` is an exact integer identity; cancellation later uses `g!=0`. |
| N7 | PASS | `reflected_third_determinant_identity` and `reflected_third_determinant_dvd_endpoint_squares` are symbolic Lean theorems. |
| N8 | PASS | `target_reflected_third_inner_ne_zero` checks all 27 coefficient/sign cases from exact ratio bounds and the explicit target threshold. |
| N9 | PASS | `reflected_third_inner_abs_lt` and `reflected_endpoint_square_product_lt_of_determinant` retain the exact factor `54r`. |
| N10 | PASS | Ordinary-kernel `interval_cases` proves the stronger `<10^200` statement; exact Python independently reconstructs all 27 integers. |
| N11 | PASS | `no_reflected_three_bucket_of_packing_bounds` uses only positivity, the exact factorization, the two strict bounds, `g<=G_k`, and the cutoff. |
| Arbitrary-owner composition | OPEN | No theorem maps an arbitrary all-owner certificate to N3 without discarding or regrouping additional live components. |

The public cutoff and generic tail packing theorems are

```text
target_reflected_packing_cutoff_certificate_tail1000
no_reflected_three_bucket_tail1000_of_packing_bounds.
```

The equation-facing supplied-slice name is
`no_four_solution_of_exact_center_reflected_three_bucket_tail1000`.  It and
the two public numerical interfaces above compile with only
`[propext, Classical.choice, Quot.sound]`.

## Exact 27/12/15 audit

| row | all pairs | legacy `<10^120` | newly `<10^200` | newly closed positions | row-maximum digits |
|---:|---:|---:|---:|:---|---:|
| 5 | 2 | 2 | 0 | none | 49 |
| 7 | 3 | 3 | 0 | none | 71 |
| 9 | 4 | 4 | 0 | none | 104 |
| 11 | 5 | 3 | 2 | `r=4,5` | 125 |
| 13 | 6 | 0 | 6 | `r=1,...,6` | 163 |
| 15 | 7 | 0 | 7 | `r=1,...,7` | 197 |
| **total** | **27** | **12** | **15** |  |  |

The verifier asserts all of the following as exact Python-integer facts:

```text
total_pairs = 27,
legacy_closed_pairs = 12,
newly_closed_pairs = 15,
all cutoff values < 10^200 < 10^1000,
row maximum digit counts = [49,71,104,125,163,197].
```

The largest exact cutoff, at `(15,7)`, is recorded in the companion findings
file.  No logarithm or floating-point comparison is used.

## Boundary and falsification matrix

| fixture or boundary | verdict | reason |
|---|---|---|
| `k=9`, `(n,d)=(2,1)` telescope | PRESERVED | Exact equation, but `1<10^1000`; N1 is false. |
| `k=15`, `(n,d)=(4,1)` telescope | PRESERVED | Same cutoff failure. |
| Frozen 121-digit fourth-order CRT representative | OUTSIDE | Below `10^1000`, fails fifth order, the short window, and the exact equation. |
| Fifth Hensel extension of that representative | OUTSIDE | Satisfies the fifth congruence package, but has a nonzero block difference, fails the upper residual window by over 603 decimal orders, remains below `10^1000`, and uses owners `(1,2,4)` at `k=5` rather than center/reflected owners. |
| Unit component `P=1`, `Q=1`, or `R=1` | INCLUDED algebraically | N3 asks only positivity.  The packing proof does not cancel a component or assume `1<P,Q,R`. |
| Empty all-owner bucket | NOT PROMOTED | It is exactly the unit `1`.  The all-owner layer may contain it, but this theorem does not count it as a third live owner or derive N3 from it. |
| `r=1` | INCLUDED | Lower endpoint of `1<=r`. |
| `r=(k-1)/2` | INCLUDED | For odd `k`, this is exactly the largest integer satisfying `r<(k+1)/2`. |
| Reversing the reflected endpoints | INCLUDED once | The determinant uses both endpoints.  There are 27 unordered pairs and 54 oriented coefficient views. |
| MalekZ all-moduli families | UNAFFECTED | The closure uses the exact block equation, exact residual window, and archimedean packing, not a pure congruence obstruction. |

## Circularity and strength audit

The following implications are forbidden and are not used:

```text
at least three extracted owners -> exactly three owners,
three selected owners -> their product is the whole cleaned gap,
arbitrary three owners -> center plus reflected pair,
unit bucket -> nonunit live component,
27 closed placements -> OddThueTail1000Hypothesis.
```

The headline assumes the exact N3 decomposition.  That premise is much
stronger than the already-banked statement that one owner assignment contains
at least three distinct live witnesses, and much weaker than the complete odd
tail only in the sense that it selects one special subcase.  No target-strength
lemma is hidden behind “assembly.”

## Reproduction and kernel gate

Run:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t1_all_owner/test_reflected_three_bucket_verify.py
python3 -m \
  compute.campaign686.agent_t1_all_owner.reflected_three_bucket_verify \
  --compact
lake env lean ErdosProblems/Erdos686ReflectedThreeBucketDeterminant.lean
```

Current focused reproduction:

```text
2 passed,
160083 exact determinant identities,
144531 signed determinant fixtures,
27 exact cutoff rows,
12 legacy closed pairs,
15 newly closed pairs.
```

The module contains no `native_decide`, `sorry`, `admit`, or new axiom.  The
cutoff, generic tail packing, equation-facing endpoint, and headline surfaces
report only `[propext, Classical.choice, Quot.sound]`.

## Shared-document integration checklist

The equation-facing wrapper is compiled and named.  Campaign integration must
update, without overstating, these locations:

1. `compute/campaign686/approach_registry.md`, Target 1 row `T1-5L`.
2. `compute/campaign686/audit.md`, immediately after the three-cleaned-bucket
   dependency tree.
3. `PROGRESS_Erdos686.md`, executive three-bucket ledger and current proof
   obligations.
4. `FRONTIER.md`, the Erdős #686 three-bucket/reflected paragraph.
5. `compute/campaign686/final_residual_hostile_audit.md`, only if this
   restriction is explicitly added to the residual dependency ledger.
6. The historical reflected-three-bucket findings/audit, by cross-reference
   rather than deletion of their correct `10^120` 12/15 boundary.
7. `ErdosProblems.lean`, `Audit.lean`, `proofs.yaml`, and
   `attestations.json`, using the final public theorem names and actual axiom
   output.
