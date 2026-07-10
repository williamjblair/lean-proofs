# Erdős 686 campaign intake audit

This audit follows the dependency-tree discipline in `compute730/audit.md`.
It is updated as candidates enter or leave the proof path.

## Baseline

- Focused terminal module compiles.
- `proofs.yaml` and the manifest-tracked `Audit.lean` section agree on 349
  theorem names.
- The axiom audit checks 753 printed theorem surfaces and permits only
  `[propext, Classical.choice, Quot.sound]`.
- `attestations.json` contains 349 non-null clean attestations, including
  345 for problem 686.

## Dependency tree: odd-tail prime-power restriction

1. Exact block equation. **Banked premise.**
2. `d | 3*B_k(n)`. **Proved on paper; Lean in progress.**
3. Unique localization of `p^e` for prime `p>=k`. **Proved on paper; Lean in progress.**
4. Local square/cubic Taylor lift. **Proved on paper; exact coefficient tests pass; Lean in progress.**
5. Explicit `C_k` power inequalities. **Exact arithmetic reproduced.**
6. `p^(2e)<A_k*d`, center `p^(3e)<A_k*d`. **Paper consequence complete; not a tail proof.**

Verdict: genuinely new proper restriction.  It is not equivalent to
`OddThueTailHypothesis`, because gaps supported on primes below `k` satisfy
the restriction vacuously.

## Dependency tree: reflection compression

1. Reflection congruence `S | reflectionCoeff(k)*B_k(n)`. **Banked.**
2. Per-factor `gcd(S,n+i) | d+k+1-2i`. **Banked.**
3. Finite-product gcd compression. **Proved on paper; Lean in progress.**
4. `S | reflectionCoeff(k)*reflectionProduct(k,d)`. **Paper consequence complete.**

Verdict: genuinely new but insufficient.  Exact smooth row-prefix points and
two stronger synthetic counterexamples satisfy the reflection conditions and
still fail row divisibility or the equation.

## Dependency tree: greatest-prime-factor wedge

1. `d+k-1<n` and lower-block smoothness. **Banked.**
2. `n>4d` for `k>=16`. **Elementary proof complete; Lean not yet banked.**
3. Every lower term is composite. **Immediate from banked smoothness and size.**
4. Nair-Shorey `P(product)>221k/50`. **Published theorem, externally verified; not formalized.**
5. Contradiction for `k>=25` and `50(d+k-1)<=221k`. **Paper derivation complete.**

Verdict: rigorous paper-level unbounded wedge, but not accepted by the local
kernel gate until dependency 4 is formalized.

## Mandatory falsification verdicts

- `k=9,15`, `d=1` telescopes: preserved by every new odd-tail lemma.
- `(984,3177026,4480)`: exact window and rows 1..16 reproduced; row 17 fails;
  not an equation solution.
- `(244,48502,277)`: exact window and rows 1..15 reproduced; row 16 fails;
  not an equation solution.
- Fixed-prefix claims: remain refuted.
- Congruence-only route: not used.
- Gross log-mass counting: not used.

## Current exact gaps

The terminal proof still requires both original quantified hypotheses:

```lean
OddThueTailHypothesis
LargeKSmoothHypothesis
```

The results above have not been substituted for either target.  No theorem
equivalent to a target is being counted as progress.
