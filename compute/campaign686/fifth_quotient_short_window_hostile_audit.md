# Hostile audit: Erdős 686 fifth-quotient short-window checkpoint

Verdict: **PASS for the generic Lean consequences and exact-computational
ledger; NOT LEAN-BANKED for the universal 3,024-position nonvanishing claim.**

The checkpoint is a proper strengthening of the equation-facing
three-bucket surface.  It does not prove the remaining simultaneous nonzero
branch or Erdős #686.

## 1. Dependency tree and per-node verdict

```text
target exact-three-bucket position
|
+- Q1 exact product identity for opposite factors                 LEAN PASS
|  +- X < U*d, Y < U*d, |T| < B*g^2*d
|  `- d^2*A*|z| = g^2*X*Y*|T|
|
+- Q2 fourth numerator identity                                  LEAN PASS
|  `- P*w = 27*C^2*A*z + K*g^4, d=P*M
|
+- Q3 normalized fifth numerator                                 LEAN PASS
|  `- N = 27*w + M*R1*g^4
|
+- Q4 normalized divisibility and nonzero input                  LEAN PASS
|  `- P | N and N != 0
|
+- Q5 exact eliminant                                            LEAN PASS
|  `- d^4*P*N = g^4*J(X,d)
|
+- Q6 3,024-row coefficient and sign ledger                     EXACT PYTHON PASS
|  +- 1,008 nonreflected triples, three owners each
|  +- zero critical points inside all rational intervals
|  +- zero endpoint sign changes
|  +- minimum leading margins > 1
|  `- lower-degree majorants < 10^46
|
`- Q7 target cutoff d >= 10^1000                                EXACT PYTHON PASS
   `- leading margin*d^5 > remainder*d^4
```

Q1--Q5 are kernel-checked generic theorems.  Q6--Q7 are deterministic exact
integer/rational computations, not a Lean table certificate.  Therefore the
combined statement “all 3,024 target-window fourth and fifth numerators are
nonzero” is an exact-computational claim only in this checkpoint.

## 2. Quantified bounds replacing informal uniformity

There is no use of “essentially bounded” or asymptotic notation.

- `B = 9*|C|*U^3 + 108*|D*delta| + 180*|E*delta|`.
- `A*|z| < U^2*B*g^4*d`.
- `W = 27*|C|^2*U^2*B+|K|` and `|w| < W*g^4*M`.
- `V = 27*W+|R1|` and `|N| < V*g^4*M`.
- If `P|N` and `N!=0`, then `P^2 < V*g^4*d`.
- For every scanned eliminant, `|X|<=36d` makes each monomial of total degree
  below five at most `|coefficient|*36^degree_X*d^4`.
- The worst normalized remainder sum is exactly
  `5803459849500468008887094102834483923255296000 < 10^46`.
- The worst fourth remainder sum is exactly
  `214942957388906222551373855660536441602048000 < 10^46`.
- Both minimum leading margins are strictly greater than one, so
  `d>=10^1000` strictly dominates either remainder majorant.

## 3. Finite-domain boundary

The enumeration is exactly the six rows `{5,7,9,11,13,15}`.  Reflected
triples containing the center and a symmetric pair are excluded, leaving
exactly `8+32+80+160+280+448=1008` triples.  Cycling over their three owners
gives exactly `3024` positions.

The exclusion is load-bearing: reflected positions are not silently covered
by this ledger.  Rows outside the six-row target list are also not covered.

The root brackets are adjacent denominator-100,000 rationals:

```text
k=5:  (131950,131951)    k=7:  (121901,121902)
k=9:  (116652,116653)    k=11: (113431,113432)
k=13: (111253,111254)    k=15: (109682,109683)
```

The verifier widens the induced residual-ratio interval by exactly `1/100`.
This padding is checked against the full corrections obtained by linearizing
the two power windows, not just against `3*(k-1)/d`.  For owner `s` the exact
corrections are

```text
3*(100000-hi*k)/(hi-100000)+3*s,
3*(100000*k-lo)/(lo-100000)+3*s.
```

The six row maxima are respectively

```text
10556/213, 2194218/21901, 699912/4163,
1134310/4477, 1335036/3751, 2303322/4841.
```

Each is below `1000`, and the verifier checks exactly that
`1000/10^1000 < 1/100`.  All endpoint values, correction bounds, and
critical-point comparisons use `Fraction`, not floating point.  The lower
endpoint absorbs the correction from the power window centered at `n+k`; the
upper endpoint absorbs the correction from the power window centered at
`n+1`.

## 4. Sign certificate audit

For either sparse form `a*x^5+b*x^2+c`, the derivative is
`x*(5*a*x^3+2*b)`.  The target intervals are positive.  Thus the only possible
interior nonzero critical point is determined by
`x^3=-2*b/(5*a)`.  The verifier compares this rational cube exactly with the
cubes of both rational endpoints.  Across all 3,024 positions it finds zero
interior critical points and zero endpoint sign changes for both the fourth
and normalized fifth eliminants.

Endpoint equality is treated as failure (`product <= 0`), not as a favorable
sign.  The recorded minimum absolute endpoint margins are positive and frozen
by pytest.

## 5. Algebra reconstruction audit

The verifier reconstructs local product coefficients by multiplying the
affine factors.  It reconstructs `K`, `R1`, and `R2` from their explicit
integer formulas and checks

```text
reducedFifth(d) = 27*K+d*R1+d^2*R2
```

at four exact gap values for every position, for 12,096 decomposition checks.
It independently builds the sparse bivariate eliminant and compares its full
degree-five homogeneous coefficient dictionary against the displayed
three-term form.  A coefficient mismatch raises an exception before a report
is emitted.

## 6. Hostile routes rejected

- **Cyclic multiplication is exponent-wrong.**  The three inequalities
  `P_s^2<V_s*g^4*d` multiply to a bound with too much `d` and do not contradict
  `P_1P_2P_3=d/g`.
- **The fourth-quotient sign lattice is mixed.**  Nonvanishing does not imply
  a common sign, so summing or multiplying signs is not a cutoff argument.
- **A sixth congruence iteration is insufficient by itself.**  The exact
  exponent-166 fixture has all three fifth congruences and all named
  quotients nonzero, but fails both the target upper window and block equation.
- **`R1!=0` is not a proof that `w!=0`.**  Fourth nonvanishing is checked by a
  separate fourth eliminant ledger; it is not inferred from the normalized
  numerator.
- **A Python exhaustive scan is not a kernel theorem.**  The absence of an
  ordinary-`decide` or `norm_num` row certificate is recorded explicitly.

## 7. Axiom and forbidden-token boundary

The direct Lean compile prints the five new theorem axiom sets within

```text
[propext, Classical.choice, Quot.sound].
```

No new `native_decide`, `sorry`, `admit`, custom `axiom`, `unsafe`, `extern`,
or `implemented_by` construct is used.  The finite Python ledger cannot be
promoted to the attested Lean surface until an ordinary-kernel certificate is
added and checked.

## 8. Exact remaining gap

After the exact-computational row scan, the unresolved statement is:

> For each of the 1,008 nonreflected target triples with `d>=10^1000`, exclude
> the simultaneous system consisting of the three nonzero cyclic third,
> fourth, and normalized fifth quotient identities together with the exact
> block equation and the verified short-window bounds.

No lemma equivalent to that statement is claimed here.

## 9. Reproduction

```bash
lake env lean ErdosProblems/Erdos686FifthLocalLift.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/test_fifth_quotient_short_window_verify.py
PYTHONDONTWRITEBYTECODE=1 \
  python3 compute/campaign686/fifth_quotient_short_window_verify.py \
  >/tmp/fifth_quotient_short_window.json
python3 -m json.tool /tmp/fifth_quotient_short_window.json >/dev/null
```
