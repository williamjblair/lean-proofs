# Uniform incomplete-block campaign: dependency tree

Date: 2026-07-10

Status labels: `PROVED`, `EXACT-CHECKED`, `FALSE`, `OPEN`.

## Global Erdős #730 route

```text
N0  Infinitely many consecutive equal-support pairs                    OPEN
 |
 +-- N1  Kummer transition criterion                                   PROVED
 +-- N2  Family n+1=PQ, 2n+1=3RS and branch separation                 PROVED
 +-- N3  Four Phi_L formulas and integrality                           PROVED
 +-- N4  p-adic isometry of each admissible branch map                 PROVED
 +-- N5  Top-range congruence structure                                PROVED
 |    `-- N5b  Quantitative upper-bound-sieve constant                 OPEN
 `-- N6  Incomplete-block count plus first moment                      OPEN
      |
      +-- N6.1  Exact full p^(2r)-block count                          PROVED
      +-- N6.2  Claimed uniform count on every interval                FALSE
      +-- N6.3  Sparse-Fourier completion proving N6.2                 IMPOSSIBLE
      |          (the target itself has an affine high-a counterexample)
      +-- N6.4  Maximal-r half-band payment for 2s<r                    PROVED
      |          normalized contribution < 0.01 for X >= 2^57; Lean-banked
      +-- N6.5  Signed Fourier inequality (20) outside old band         FALSE
      |    +-- exact energy + sparse Gauss completion                  PROVED
      |    +-- post-completion triangle majorant                       INSUFFICIENT
      |    `-- exact p=5,r=432,s=176,a=688 witness                     EXACT-CHECKED
      +-- N6.6  Corrected incomplete-block estimate for s>=r/2         OPEN
      `-- N6.7  Explicit global budget below 1                         OPEN
```

The campaign now changes N6.2, N6.4, and N6.5: the original uniform lemma
and its proposed signed repair are false, while the full half-band is paid
below one percent.  It does not challenge the audited algebraic nodes
N1--N5, and it does not prove N0.

## Counterexample dependency tree

```text
U0  Uniform incomplete-block lemma as quantified in the prompt         FALSE
 |
 +-- U1  Freeze the branch map
 |    G(k)=A p^a k^2 + (p^a u+b)k+v,
 |    p does not divide b                                               PROVED
 |
 +-- U2  Choose the admissible Q branch and a=2r
 |    G(k) = b k+v (mod p^(2r))                                        PROVED
 |    (it extends when s=max(2r-a,0) is below kappa_p r)
 |
 +-- U3  Translate the interval
 |    for any rho choose k0 with b k0+v=rho (mod p^(2r)); then
 |    G(k0+t)=rho+bt (mod p^(2r))                                      PROVED
 |
 +-- U4  Pigeonhole an aligned residue class
 |    after removing one forbidden least digit, at least
 |    (H-1)H^(r-1)/(bp) restricted y share one class rho mod bp         PROVED
 |
 +-- U5  Exact valuation
 |    the removed digit is exactly the output residue corresponding to
 |    c(k)=0 mod p; differences within rho mod bp give t=0 mod p        PROVED
 |
 +-- U6  Interval size
 |    all hit parameters t=(y-rho)/b span less than p^r/b, hence fit
 |    in N=ceil(p^r (log p^r)^C)                                       PROVED
 |
 `-- U7  Contradiction
      lower count >= (H-1)H^(r-1)/(bp), while the claimed main term is
      O((H^2/p)^r r^C); their ratio grows like
      (p/H)^r / poly(r)                                                 PROVED
```

Here `H=(p+1)/2`, and `p/H=2p/(p+1)>1`.  The construction works for each
of `p=5,7,11` on the Q branch.  It therefore refutes uniformity in `p`,
branch, `a`, congruence class, and interval.

## What a viable replacement must change

At least one quantifier must be weakened:

1. remove the whole near-affine band
   `s=max(2r-a,0) < (log_p(p/H)-epsilon)r` from the analytic lemma and pay
   for its valuation rarity separately;
2. average over interval translations instead of bounding every interval;
3. use blocks of length comparable to `p^(2r)`; or
4. replace the `2r`-digit density by a bound that recognizes the affine
   degeneration.

Sparse-frequency completion cannot prove N6.2 or the stronger signed
inequality N6.5.  The entire half-band `2s<r` is instead paid by the exact
maximal-r valuation bound in `repair/half_band_payment_findings.md`, whose
arithmetic spine is Lean-banked.  The corrected analytic node is N6.6:
an incomplete-block estimate with a globally payable error for `s>=r/2`.
