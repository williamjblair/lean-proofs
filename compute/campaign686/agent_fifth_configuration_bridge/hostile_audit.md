# Hostile audit: fifth-quotient configuration bridge

## Verdict

The Lean bridge is a genuine construction theorem, not a contradiction and
not a restatement of Erdős 686.  From one actual selected-three
factorization it constructs the third quotient z, reduced fourth quotient w,
and normalized fifth numerator N.  It proves the two displayed quotient
identities, the true fifth-order consequence P divides N, and w and N are
nonzero.

The all-owner corollary is also genuine.  It extracts any imported
nonreflected owner/left/right triple and absorbs every omitted bucket into a
new loss g.  It does not claim that this enlarged g satisfies the original
bounded-loss estimate.

The exact sign scan rules out the most immediate simultaneous closing route:
the canonical weighted fourth signs and canonical weighted normalized-fifth
signs are mixed for every one of the 1,008 nonreflected triples.

## Dependency tree

1. allOwner_selected_three_fifth_quotient_configuration
   1. ordinary-kernel metadata for all 3,024 imported positions;
   2. allOwner_gap_decomposition_at_three;
   3. positivity of the three selected residuals;
   4. exact signed residual casts;
   5. direct_selected_three_fifth_quotient_configuration.
2. direct_selected_three_fifth_quotient_configuration
   1. second-, third-, fourth-, and fifth-order local lifts;
   2. selected-three algebraic compositions;
   3. exact third quotient z from P squared divisibility;
   4. exact reduced fourth quotient w from P divisibility;
   5. exact normalized numerator N and P divides N;
   6. the existing equation-facing nonvanishing wrapper for w and N.
3. fifth_configuration_bridge_verify.py
   1. the independently tested exact coefficient and eliminant recurrences in
      fifth_quotient_short_window_verify.py;
   2. an independent reconstruction check of each degree-five homogeneous
      part;
   3. exact rational endpoint, critical-point, and remainder comparisons;
   4. exact cyclic cross weights and sign counts.

## Per-node verdicts

| Node | Verdict | Reason |
| --- | --- | --- |
| Imported-position metadata | proved in Lean | Ordinary-kernel decision over the exact finite list. |
| Three-bucket extraction | proved in Lean | Three successive product-erasure identities, with all omitted factors visible in g. |
| Signed residual data | proved in Lean | Uses the equation window for positivity, then exact natural-to-integer casts. |
| Construction of z | proved in Lean | Witness extracted from P squared divisibility of the actual third obstruction. |
| Construction of w | proved in Lean | Witness extracted from the reduced fourth divisibility identity. |
| Construction of N | proved in Lean | Defined by the normalized fifth identity; P divides N is proved. |
| Nonvanishing of w and N | proved in Lean | Applied to actual product, opposite-product, quotient, and block-equation identities. |
| All-owner bounded loss after extraction | not claimed | Omitted nonunit buckets multiply the new g. |
| One-sided simultaneous sign contradiction | falsified | Both canonical weighted sign triples are mixed in all 1,008 cases. |
| Full Erdős 686 conclusion | open | No simultaneous magnitude or gcd coupling closes the nonzero branch. |

All printed axiom sets are exactly propext, Classical.choice, and Quot.sound.
There is no forbidden evaluator and no private unproved lemma.

## Exact theorem surfaces

For every imported position p, every target-scale d, and natural data
P,Q,R,g,a,b,c satisfying

    d = g P Q R,

the three exact signed square residual identities, P divides n+p.owner, and
the block equation, the direct theorem produces integers z,w,N satisfying

    T = P^2 z,
    P w = 27 C^2 b c z + K g^4,
    N = 27 w + (g Q R) R1 g^4,
    P divides N,
    w != 0,
    N != 0.

The all-owner theorem has the same conclusion with the selected buckets and
cofactors from the supplied AllOwnerAssemblyThirdNonzeroCertificate.  Its
loss is exactly

    original grouped loss
      times the product of every unselected full-grid bucket.

No upper bound for that product appears in the theorem.

## Exact finite sign audit

For each cyclic owner s in a nonreflected triple, set

    A_s = -9 C_s,
    B_s = 180 E_s delta_s,
    G_s = 108 D_s delta_s.

The three third rows have the form

    T_s = A_s t + B_s g^2 d + G_s g^2.

For cyclic order 1,2,3, the canonical cross weights are

    L_1 = A_2 B_3 - A_3 B_2,
    L_2 = A_3 B_1 - A_1 B_3,
    L_3 = A_1 B_2 - A_2 B_1.

The verifier checks exactly that the L-weighted A and B sums vanish and that
all 3,024 weights are nonzero.  Hence

    sum_s L_s T_s = Gamma g^2,
    Gamma = sum_s L_s G_s.

After multiplying each fourth identity by the positive clearing factors
a_s P_s^2 and a common multiple of the C_s squared, the sign of each weighted
left side is sign(L_s w_s).  The analogous normalized identity has weighted
left-side sign sign(L_s N_s).

All sign decisions include the lower-degree eliminant terms.  For
x = X/d, the exact degree-five parts are

    -243 C^3 x^5 + 4860 C^2 E delta x^2

for w and

    -6561 C^3 x^5 + 131220 C^2 E delta x^2 + R1

for N.  At both exact rational endpoints the verifier finds the same nonzero
sign, finds no positive critical point inside the interval, reconstructs the
degree-five homogeneous part of each sparse eliminant, and verifies that the
endpoint margin times 10^1000 exceeds the full lower-degree majorant.

The frozen exact totals are:

| Claim | Exact count |
| --- | ---: |
| Nonreflected triples | 1,008 |
| Cyclic positions | 3,024 |
| sign(w) = -sign(C) | 3,024 |
| sign(N) differs from sign(w) | 90 |
| Nonzero canonical weights | 3,024 |
| Triples with mixed weighted w signs | 1,008 |
| Triples with mixed weighted N signs | 1,008 |
| Positive Gamma | 502 |
| Negative Gamma | 506 |

The per-row triple counts are 8, 32, 80, 160, 280, and 448.  The per-row
normalized sign-flip counts are 0, 4, 8, 16, 26, and 36.

## Boundary and circularity checks

- Reflected triples are excluded exactly as in the imported finite table.
  No result here silently extends to them.
- Only k in 5,7,9,11,13,15 is covered.
- Unit selected buckets are allowed; only positivity is needed.
- No selected bucket is assumed prime, and no pairwise coprimality is used.
- Positivity of g follows from d > 0 and the selected product
  factorization; it is not an extra premise.
- If every omitted bucket is a unit, the enlarged loss reduces
  mathematically to the original grouped loss.  The present Lean theorem does
  not package that support hypothesis or the resulting bound.
- Individual fourth/fifth nonvanishing and P divides N do not imply a
  simultaneous contradiction.  Multiplying the three component estimates
  has the wrong exponent, and the exact weighted signs are not one-sided.
- The all-owner third-nonzero field is supplied by the certificate but is not
  used to fake the fifth-order conclusion.  All fifth-order data are rebuilt
  from the local equation.

## Exact remaining gap

The proved bridge leaves one explicit kind of missing input: a simultaneous
relation between at least two selected buckets and the enlarged loss, strong
enough to beat the exponent-neutral individual bounds.  No such relation is
assumed or proved here.  One concrete quantified candidate is:

    There exists H in the natural numbers such that, for every target
    solution and every supplied all-owner certificate, there is an imported
    nonreflected position and two distinct roles r,s among owner,left,right
    for which P_r^2 <= H g^2 and P_s^2 <= H g^2, where g is exactly the
    omitted-bucket loss constructed for that position.

This statement is not currently banked for any explicit H.  It is a
genuinely stronger simultaneous estimate, not a renamed form of either
constructed quotient identity.

## Reproduction

    lake env lean ErdosProblems/Erdos686FifthQuotientConfigurationBridge.lean
    python3 -m pytest -q compute/campaign686/agent_fifth_configuration_bridge/test_fifth_configuration_bridge_verify.py
    python3 -m compute.campaign686.agent_fifth_configuration_bridge.fifth_configuration_bridge_verify
