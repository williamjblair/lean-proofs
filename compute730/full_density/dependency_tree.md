# Erdős #730 full-density candidate: dependency tree

Audit date: 2026-07-13

Status vocabulary:

- `IMPORTED`: used as a named external theorem, not reproved here.
- `EXACT-CHECKED`: all finite arithmetic was independently reproduced by
  `verify.py` and `test_verify.py`.
- `PAPER-PROVED`: a quantified argument is present in the submitted proof and
  survives this hostile audit.
- `KERNEL-BANKED`: the stated node, or the explicitly named subnode, has a
  no-`sorry` Lean theorem whose axiom footprint is contained in
  `[propext, Classical.choice, Quot.sound]`.
- `LEAN-OPEN`: no kernel-checked realization has yet been established by this
  intake lane.

The labels are deliberately cumulative only where stated.  In particular,
`PAPER-PROVED` never means `LEAN-PROVED`.

```text
H0  liminf_X Good(X)/X > 107/2500                         PAPER-PROVED; LEAN-OPEN
 |
 +-- I1  Kummer carry theorem                                      IMPORTED
 |    +-- p does not divide B(t) iff all digits are lower-half    KERNEL-BANKED
 |    `-- N1  exact consecutive-transition criterion              KERNEL-BANKED
 |         `-- endpoint digit shifts in (5), (6), and (8)         KERNEL-BANKED
 |
 +-- N2  four-branch family and separation                         KERNEL-BANKED
 |    +-- T=5289 and four slopes/constants                         KERNEL-BANKED
 |    +-- 2PQ-1=3RS and six linear identities                     KERNEL-BANKED
 |    +-- pairwise coprimality and fixed primes                    KERNEL-BANKED
 |    `-- four Phi_L obstruction formulae                          KERNEL-BANKED
 |
 +-- N3  generic p-adic isometry and exact digit count             KERNEL-BANKED
 |    +-- common quadratic coefficient 3024*T^2                    KERNEL-BANKED
 |    +-- b_L factors supported on {2,3,41,43}                     KERNEL-BANKED
 |    +-- G mod p^j is injective/bijective under b_L a unit       KERNEL-BANKED
 |    `-- exact count (H-1)H^(d-1)                                 KERNEL-BANKED
 |
 +-- N4  bad parameter implies a witnessed obstruction             KERNEL-BANKED
 |    `-- finite union-bound count Bad(X) <= E(X)                  PAPER-PROVED
 |
 +-- N5  higher powers a>=2 contribute o(X)                        PAPER-PROVED
 |    +-- complete/padded p^r block count                          KERNEL-BANKED
 |    +-- generic dominated convergence over (p,a)                 KERNEL-BANKED
 |    +-- instantiate event summands and pointwise decay           PAPER-PROVED
 |    +-- finite M(Z) square/cuberoot/log bound                    KERNEL-BANKED
 |    +-- M(Z)/Z tends to zero                                     KERNEL-BANKED
 |    `-- terminal powers X<p^a<=C0 X specialization               PAPER-PROVED
 |
 +-- N6  fixed-depth Fourier lemma, only for a=1                    PAPER-PROVED
 |    +-- order-two half-digit parity count/error                  KERNEL-BANKED
 |    +-- effective moduli p^m, m<=r, vanish exactly               PAPER-PROVED
 |    +-- m>r completion and quadratic Gauss sum                   PAPER-PROVED
 |    +-- interval Fourier mass on one nonzero class               PAPER-PROVED
 |    `-- digit-box Fourier l1 norm                                PAPER-PROVED
 |
 +-- I2  Mertens reciprocal-prime theorem                           IMPORTED
 |    +-- N7  each fixed first-power band r                        PAPER-PROVED
 |    +-- N8  uniform tail in r                                    PAPER-PROVED
 |    `-- N9  transition range sqrt(X)<p<=Y is o(X)                PAPER-PROVED
 |
 +-- N10 top-prime classification                                  PAPER-PROVED
 |    +-- p/c>130 from Y=sqrt(X)(log X)^2                          PAPER-PROVED
 |    +-- P classes c=3,4 mod 7                                    EXACT-CHECKED
 |    +-- R classes c=5,9 mod 14                                   EXACT-CHECKED
 |    `-- Q and S impossible under p/c>130                         PAPER-PROVED
 |
 +-- I3  fixed-modulus PNT in arithmetic progressions               IMPORTED
 |    `-- N11 divisor switching and top contribution <=2/3 log 2  PAPER-PROVED
 |         +-- P: 20160 of phi(222138)=60480 classes               EXACT-CHECKED
 |         `-- R: 13440 of phi(148092)=40320 classes               EXACT-CHECKED
 |
 +-- N12 exact constant certificate                                KERNEL-BANKED
 |    `-- 4*S+(2/3)log 2 < 2393/2500                              KERNEL-BANKED
 |
 `-- N13 density complement and strict increase                    PAPER-PROVED
      `-- strict increase and density-to-upstream bridge           KERNEL-BANKED
```

## Exact imported theorem surface

The paper proof is relative to precisely these three external results.

1. For every prime `p` and nonnegative `u,v`, the `p`-adic valuation of
   `binomial (u+v) u` is the number of carries in the base-`p` addition of
   `u` and `v`.
2. There is a real constant `M` such that, for every real `z>2`,
   `abs (sum_{p<=z} 1/p - log(log z) - M) <= 4/log z`.
   The proof uses only the consequence that the displayed error tends to
   zero, plus `sum_{p<=z} 1/p = O(log log z)`.
3. For every fixed positive integer `A`, there are positive
   `K_A,kappa_A,z_A` such that for every reduced residue `a mod A` and every
   real `z>=z_A`,

   ```text
   abs (pi(z;A,a) - Li(z)/phi(A))
     <= K_A*z*exp(-kappa_A*sqrt(log z)).
   ```

   Only `A=1`, `A=222138`, and `A=148092` are used.

No fourth analytic input is hidden in an “essentially” or “standard
estimates” phrase.

## Quantified asymptotic nodes

The notation in the tree expands as follows.

- `N5`: for each branch `L`,
  `lim_{X->infinity} E_{L,a>=2}(X)/X = 0`.  The dominating series is
  `sum_p sum_{a>=2} 2/p^a < infinity`; for every fixed `(p,a)`, its extra
  factor `rho_p^floor(log_p(X/p^a))` tends to zero.
- `N6`: for each fixed integer `r>=1`, every odd prime `p`, every
  `F(t)=p*alpha*t^2+beta*t+gamma` with `p` dividing neither `alpha` nor
  `beta`, every translated interval of exactly `p^r` inputs, and every
  stated `2r`-digit box, the absolute count error is at most

  ```text
  (2r+3)*3^(2r)*p^(r-1/2)*(1+log p)^(2r+1).
  ```

- `N7`: for every fixed `r>=1` and branch `L`,

  ```text
  limsup_{X->infinity} E_{L,r}(X)/X
    <= 4^(-r)*log((r+2)/(r+1)).
  ```

- `N8`:

  ```text
  lim_{R->infinity} limsup_{X->infinity}
    sum_{r>R, p in band r} rho_p^r/p = 0.
  ```

  The order is fixed finite `r`, then `X->infinity`, then `R->infinity`.
- `N9`: `lim_{X->infinity} E_trans(X)/X=0` for
  `sqrt(X)<p<=sqrt(X)(log X)^2`.
- `N11`: for `L=P,R`,
  `limsup_{X->infinity} E_top,L(X)/X <= (1/3)log 2`.
- `H0`: with `Good(X)=X-Bad(X)`,
  `liminf Good(X)/X > 107/2500`.

## Falsification boundary

The prior false lemma asserted a square-root-scale incomplete-interval
estimate uniformly in the valuation `a`, digit depth `r`, and interval
translation.  The exact witness

```text
p=5, r=432, s=176, a=688
```

still refutes that old statement.  It does not instantiate `N6`, whose
hypothesis is `a=1` and whose constant may depend exponentially on fixed
`r`.  It instantiates `N5` (`a>=2`), which uses complete/padded permutation
blocks and dominated convergence, not incomplete quadratic cancellation.
The regression is executed in `test_verify.py`; the legacy cleared margin is
required to remain positive.

This separation is structural, not a claim that the old witness vanished.
