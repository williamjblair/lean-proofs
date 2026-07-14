# Erdős #730 full-density proof: hostile audit and kernel closure

Audit date: 2026-07-13

## 1. Verdict

**Paper verdict:** `PASS`, relative to the three classical theorem surfaces
listed below.  The submitted argument supplies a complete positive-density
proof, and its fixed-depth decomposition avoids both uniform incomplete-block
statements falsified in this repository.

**Finite certificate verdict:** `PASS`.  An independent standard-library
verifier reproduces the family arithmetic, exceptional factors, all top-range
residue tables, both full CRT class counts, the six rational logarithm bounds,
the infinite tail bound, and the final positive rational margin.

**Lean verdict:** `PASS`.  The terminal declarations are

```text
Erdos730.FullDensityTheorem.candidatePositiveDensity :
  Erdos730.FullDensityReduction.CandidatePositiveDensityClaim

Erdos730.FullDensityTheorem.pairSet_infinite :
  Erdos730.FullDensityCore.PairSet.Infinite
```

`Erdos730FullDensityTheoremAudit.lean` reports only
`[propext, Classical.choice, Quot.sound]` for both declarations.  The full
repository gate completed with

```text
PASS: 1260 headline theorem(s) clean, axioms subset of
      [propext, Classical.choice, Quot.sound]
```

The proof uses no `native_decide`, adds no axiom, and contains no admitted
declaration in the dependency cone of either terminal theorem.

## 2. Frozen source and exact target

Source artifact:

```text
/Users/williamblair/.codex/attachments/
  a6bdaeec-cb7e-456b-a0e6-d99af242235d/pasted-text.txt
SHA-256  3df2e48ca62e35dbfbd25406badf37574d910efb2ab39360ab3458f3a31c4292
lines     2818
bytes     39992
```

The source claims, with

```text
T    = 3*41*43 = 5289,
P(x) = 42*T*x+11,       Q(x) = 72*T*x+13,
R(x) = 28*T*x+5,        S(x) = 72*T*x+19,
n_x  = P(x)Q(x)-1,
```

that

```text
liminf_{X->infinity} (1/X) *
  #{x in Z : 1<=x<=X and
    supp binomial(2*n_x,n_x) =
    supp binomial(2*(n_x+1),n_x+1)}
  > 107/2500.
```

Here and below an asymptotic count is evaluated at positive integer `X`.

The full node tree and quantifier expansion are in `dependency_tree.md`.

## 3. Classical inputs and exact kernel dependency surface

The paper proof invokes three classical results.

1. **Kummer.** For every prime `p` and nonnegative integers `u,v`, the
   exponent of `p` in `binomial(u+v,u)` equals the number of carries in the
   base-`p` addition of `u` and `v`.
2. **Reciprocal-prime Mertens theorem.** There is a real `M` such that for
   every real `z>2`,

   ```text
   abs(sum_{p<=z} 1/p - log(log z) - M) <= 4/log z.
   ```

3. **Fixed-modulus PNT in AP.** For every fixed positive integer `A`, there
   are positive constants `K_A,kappa_A,z_A` such that for every reduced
   residue class `a mod A` and every `z>=z_A`,

   ```text
   abs(pi(z;A,a) - Li(z)/phi(A))
     <= K_A*z*exp(-kappa_A*sqrt(log z)).
   ```

Only moduli `1`, `222138`, and `148092` occur.  The proof does not need
uniformity as `A` varies.

The Lean realization handles these surfaces as follows.

- Pinned Mathlib supplies Kummer.
- `Erdos730Mertens.lean` proves `mertensReciprocalPrimeInput` from a
  factorial/von-Mangoldt argument and Abel summation.  Its formal error
  coefficient replaces the paper's inessential constant `4`.
- `Erdos730PNTAP.lean` derives `requiredFixedModulusPNTAPInput` from
  `PrimeNumberTheoremAnd.Consequences.chebyshev_asymptotic_pnt`, pinned at
  revision `d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96`.

The external `PrimeNumberTheoremAnd` package contains admitted declarations
in an unrelated Wiener/Fourier-decay experiment (`prelim_decay_2` and
`prelim_decay_3`).  The imported PNT-AP cone does not depend on them.
`Erdos730PNTAPAudit.lean` prints the axioms of `chebyshev_asymptotic_pnt`,
`WeakPNT_AP`, and `requiredFixedModulusPNTAPInput`; each footprint is contained
in `[propext, Classical.choice, Quot.sound]` and contains no `sorryAx`.

## 4. Per-node hostile verdicts

### 4.1 Kummer transition criterion: `PASS`

For an odd prime `p`, let `D_p` be the nonnegative integers whose base-`p`
digits are all at most `(p-1)/2`.  Kummer gives

```text
p does not divide binomial(2t,t)  iff  t in D_p.
```

Using

```text
B(n+1)/B(n) = 2(2n+1)/(n+1),
gcd(n+1,2n+1)=1,
```

the support changes only at an odd prime dividing `n+1` or `2n+1`.  The
submitted base-`p` expansions prove the exact equivalence:

- if `p^a || n+1`, the transition is harmless iff
  `(n+1)/p^a` is not in `D_p`;
- if `p^a || 2n+1`, it is harmless iff
  `((2n+1)/p^a-1)/2` is not in `D_p`.

The prime `2` divides every positive central binomial coefficient and is
separate from the displayed odd-prime conditions.

Kernel intake now proves this full if-and-only-if for every `n>0`, with
`p^a || N` expanded as positive exponent, exact factorization, and coprime
cofactor.  It also proves the prime-by-prime recurrence argument away from
`n+1` and `2n+1`.

### 4.2 Family arithmetic and branch separation: `PASS`

Independent expansion returns

```text
2P Q-1 = 3R S
        = 6048*T^2*x^2 + 2676*T*x + 285.
```

All six linear identities reproduce exactly:

```text
12P-7Q=41,   18R-7S=-43,   12P-7S=-1,
7Q-18R=1,    2P-3R=7,      S-Q=6.
```

They imply pairwise coprimality after the stated residue checks.  In
particular, `P,R` are units modulo `7`; `Q,S` are odd and `1 mod 3`; and the
constants of every branch are units modulo `41` and `43`.

The fixed prime `3` satisfies `3 || 3RS=2n_x+1`, and
`(RS-1)/2 = 2 mod 3`, so its least base-3 digit is forbidden.  The prime `7`
is not discarded: where it can divide a branch, it remains in the ordinary
event count.

### 4.3 Obstruction maps and p-adic isometry: `PASS`

For `p^a || L(x)` and `c=L(x)/p^a`, the four obstruction quantities are

```text
Phi_P(c) = (12*p^a*c^2-41c)/7,
Phi_Q(c) = ( 7*p^a*c^2+41c)/12,
Phi_R(c) = (54*p^a*c^2+129c-7)/14,
Phi_S(c) = ( 7*p^a*c^2-43c-6)/12.
```

Their alternative descriptions `cQ`, `cP`, `(3cS-1)/2`, `(3cR-1)/2`
establish integrality without a divisibility assumption being hidden.

On the unique root class `x=x_0+p^a k`, each map has the form

```text
G(k)=3024*T^2*p^a*k^2 + (p^a*u_L+b_L)k+v_L,
```

where

```text
(b_P,b_Q,b_R,b_S)=(-246T,246T,258T,-258T).
```

The independent factorization is

```text
246T = 2*3^2*41^2*43,
258T = 2*3^2*41*43^2.
```

Every branch prime is therefore coprime to `b_L`.  Factoring
`G(k_1)-G(k_2)` gives a second factor congruent to `b_L mod p`, hence

```text
v_p(G(k_1)-G(k_2))=v_p(k_1-k_2).
```

This proves bijectivity modulo every `p^d`.  Exact valuation deletes one
endpoint of the permitted units-digit interval, giving exactly
`(H-1)H^(d-1)`, where `H=(p+1)/2`.  The executable suite exhausts this digit
count for `p=3,5,7,11`, both endpoints, and depths `1` through `4`; the
general count is the direct product argument above.

Kernel intake now proves all four cleared obstruction formulas, all four
root-progression substitutions with common coefficient `3024*T^2`, the exact
residual coefficients `(-246T,246T,258T,-258T)`, their prime support
`{2,3,41,43}`, the generic p-adic bijection, and the digit-box cardinality.

### 4.4 Event coverage and partition: `PASS`

Pairwise coprimality assigns every nonfixed transition prime to one branch.
Thus `Bad(X)<=E(X)`; injectivity of this assignment is not needed because
`E` counts obstruction quadruples and the proof uses a union bound.

Kernel intake now proves the load-bearing pointwise coverage statement:
every positive bad parameter has a witnessed odd-prime drop or entry
obstruction with all valuation and cofactor fields explicit.  The finite
cardinality union bound, the four disjoint range split, and the normalized
bad-density comparison are also kernel-proved.

The partition is disjoint and exhaustive:

```text
a>=2;
a=1 and p<=sqrt(X);
a=1 and sqrt(X)<p<=Y;
a=1 and p>Y,
Y=sqrt(X)(log X)^2.
```

The equality `p=sqrt(X)` is in the small range; `p=Y` is in the transition
range.

### 4.5 Higher powers: `PASS`

For `p^a<=X`, the corrected depth is

```text
r=floor(log_p(X/p^a)) >= 0.
```

The submitted block proof remains valid at `r=0`: the digit restriction is
vacuous and (37) reduces to a coarse count.  For fixed `(p,a)`, `r->infinity`
as `X->infinity`.  The exact bound is

```text
#E_{L,p,a}(X) <= (2X/p^a)*rho_p^r+1,
rho_p=(p+1)/(2p)<1.
```

The normalized summands are dominated by `2/p^a`, whose sum over primes and
`a>=2` converges.  The `+1` terms and the terminal powers
`X<p^a<=C0 X` are bounded by

```text
M(Z) <= sqrt(Z)+Z^(1/3)log_2 Z = o(Z).
```

This proves `E_{a>=2}(X)=o(X)` without any incomplete Fourier estimate.

Kernel intake now proves the finite complete/padded residue-block inequality,
including `r=0`, the exact natural bound

```text
M(Z) <= floor(sqrt Z) + floor(cuberoot Z)*floor(log_2 Z).
```

It also proves the majorant `sum_p sum_(a>=2) 2/p^a` summable, a generic
Tannery dominated-convergence theorem for contributions under that exact
majorant, and `M(Z)/Z -> 0`.  The concrete event specialization is now also
kernel-expanded.  For every branch `L`, prime power `p^a`, and `X`, put

```text
U = floor(X/p^a),  r = floor(log_p U),  H = (p+1)/2.
```

The formalized root-progression injection and p-adic permutation give the
unconditional, depth-zero-safe inequality

```text
#E_{L,p,a}(X) <= (floor((U+1)/p^r)+1) H^r.
```

If `p^a<=X`, the explicitly normalized consequence used by the proof is

```text
#E_{L,p,a}(X)/X <= (4/p^a) rho_p^r
                       = 2*higherPowerEnvelope(X,p,a).
```

If `X<p^a`, the unique root class gives `#E_{L,p,a}(X)<=1`.  Every occurring
pair satisfies `p^a<=380827X`, so after summing the exact witness ledger over
the four branches the kernel theorem is

```text
normalizedHigherPowerWitnessCount(X)
  <= 4*(2*sum_{p prime,a>=2} higherPowerEnvelope(X,p,a)
        + M(380827X)/X).
```

Tannery and the terminal pair estimate make the displayed majorant tend to
zero.  Thus the concrete higher-power range is now kernel-proved to be
`o(X)`, not merely paper-proved.

### 4.6 Fixed-depth Fourier lemma: `PASS`

The lemma is correctly scoped: `r` is fixed, `a=1` in its application, and
its constant depends on `r`.  Replacing the attachment's big-O display by
the inequality actually proved, its conclusion is

```text
abs(count - |A|/p^r)
 <= (2r+3)*3^(2r)*p^(r-1/2)*(1+log p)^(2r+1).
```

For effective frequency modulus `p^m` with `m<=r`, the length-`p^r`
interval is a union of complete residue systems and the sum is exactly zero.
For `m>r`, completion leaves one nonzero class modulo `p`; the complete
quadratic Gauss sum has magnitude `p^((m+1)/2)`.  Layer cake gives interval
Fourier mass at most `(p^m/p)(3+log(p^r))`, and the digit-box Fourier
`l^1` mass is at most `p^(2r)(3+log p)^(2r)`.  Multiplication gives the
displayed explicit bound.

There is no uniform claim in `r`, `a`, or interval length here.

The kernel development proves the finite Fourier inversion, complete-sum
vanishing, degenerate prime-power Gauss bound, shifted-grid frequency mass,
digit-box `l^1` bound, and the translated interval hit-count estimate in
`Erdos730FixedDepthFourier.lean`.  The axiom audit for
`fixedDepth_intervalHitCount_le` contains only the standard three axioms.

### 4.7 Small first powers and uniform r-tail: `PASS`

For the unique band `p^(r+1)<=X<p^(r+2)`, fixed `r` aggregation yields

```text
limsup E_{L,r}(X)/X
 <= 4^(-r)*log((r+2)/(r+1)).
```

The Fourier discrepancy is summable because, for fixed `r`,

```text
sum_{n>X^(1/(r+2))} n^(-3/2)(1+log n)^(2r+1) -> 0.
```

The terminal blocks contribute `o(X)` by `pi(U)<=2U/log U` with
`U=X^(1/(r+1))`.

The separate padded-block estimate

```text
E_{L,p,1}(X) <= 3(X/p)rho_p^r
```

proves the double limit

```text
lim_{R->infinity} limsup_{X->infinity}
  sum_{r>R,p in band r} rho_p^r/p = 0.
```

This is the load-bearing order of limits.  Fixed `p=5,7` eventually lies in
the exact tail estimate; it is never passed to the Fourier lemma.

`Erdos730SmallPrimeEvents.lean` now connects this analysis to the concrete
obstruction ledger.  Its exact per-fiber bound retains the natural block
floor `(X/p+1)/p^r`, converts the branch progression to the quadratic phase,
and pays

```text
relaxedDigitDensity(r,p)/p + 1/X
  + fixedDepthFourierErrorConstant(r)*fixedDepthFourierWeight(r,p)
  + p^r/X.
```

After summing the four branches and assembling the uniform depth tail, the
kernel theorem is

```text
limsup normalizedSmallPrimeWitnessCount atTop
  <= 4*densityBudgetSeries.
```

### 4.8 Transition range: `PASS`

The direct multiple count gives

```text
E_trans(X)
 <= 4X*sum_{sqrt(X)<p<=Y}1/p + 4pi(Y).
```

Mertens makes the reciprocal-prime sum `o(1)`, and PNT gives
`pi(Y)/X=O(log X/sqrt X)->0`.  Hence `E_trans(X)=o(X)`.

The transition event count, reciprocal-prime band limit, and normalized
limit are kernel-proved in `Erdos730TransitionDensity.lean`.

### 4.9 Top digit classification: `PASS`

For sufficiently large `X`, `(log X)^4>130C0` and `Y>43`.  If `p>Y` and
`L(x)=pc`, then `p/c>130` and `p^2>L(x)`, so the valuation is exactly one.
The unit-residue tables were exhaustively reproduced:

| branch | modulus | numerator residues | necessary surviving classes |
|---|---:|---|---|
| P | 7 | `3,5,6` | `c=3,4 mod 7` |
| Q | 12 | `7` | none |
| R | 14 | `6,10,12` | `c=5,9 mod 14` |
| S | 12 | `7` | none |

The Q/S exclusions are explicitly conditional on `p/c>130`; the proof does
not extrapolate them to the short-prime regime.

`Erdos730DivisorSwitching.lean` formalizes the four branch classifications,
including the Q/S zero contributions and the P/R congruence classes.

### 4.10 Divisor switching and PNT-AP: `PASS`

The full enumerations are

```text
A_P=222138: phi(A_P)=60480, allowed=20160=phi(A_P)/3;
A_R=148092: phi(A_R)=40320, allowed=13440=phi(A_R)/3.
```

For a fixed periodic allowed set `C mod A`, partial summation is quantified
by `N_C(u)=delta*u+O_A(1)` and yields

```text
sum_{c<=Z/Y, c mod A in C} Li(Z/c)
 = delta*Z*log(log Z/log Y)+o(Z).
```

The PNT-AP errors sum to at most

```text
K_A*Z*(1+log(Z/Y))*exp(-kappa_A*sqrt(log Y))=o(Z).
```

Dropping the lower cutoff `p>Y` introduces at most
`(Z/Y)*pi(Y)=O(Z/log Y)=o(Z)` pairs.  Consequently each of P and R has
normalized limsup at most `(1/3)log 2`, while Q and S contribute zero.

The Lean proof derives the needed fixed-modulus prime-counting limit from the
axiom-clean `chebyshev_asymptotic_pnt` cone described in Section 3.  It then
proves the divisor-switching partial summation and the combined top-range
limsup bound `<= (2/3) log 2`.

### 4.11 Rational certificate and density transfer: `PASS`

The independent exact outputs are

```text
S upper =
  11117760449158646497 / 89848527388139520000,
log(2) upper = 1123/1620,
total upper =
  21498408212212214497 / 22462131847034880000,
2393/2500 - total upper =
  2344391769572639 / 22462131847034880000 > 0.
```

Thus the paper estimates give `limsup Bad(X)/X<2393/2500`, and complementing
gives `liminf Good(X)/X>107/2500`.  Since both positive linear forms `P,Q`
are strictly increasing, `n_x=PQ-1` is strictly increasing, so positive
density in parameters produces infinitely many distinct consecutive pairs.

`Erdos730FullDensityTheorem.candidatePositiveDensity` proves the strict
`107/2500` lower-density statement.  The terminal theorem
`Erdos730FullDensityTheorem.pairSet_infinite` transfers it to the exact
infinite set in the upstream Erdős #730 statement.

## 5. Falsification-record audit

| boundary | exact verdict |
|---|---|
| `p=5,r=432,s=176,a=688` affine witness | Still a counterexample to the old uniform lemma; routed to `a>=2`, not to the new `a=1` Fourier lemma. |
| old translated intervals at `a=2r` for `p=5,7,11` | Still fail the old main-term estimate; irrelevant to a fixed-depth `a=1` lemma and retained by the legacy suite. |
| `p=7` divides `3024T^2` | Never used in the fixed-`r` Fourier step; it lies in the exact uniform tail for large `X`. |
| Q witness `p=65,c=8` and S witness `p=1855,c=43` | Do not satisfy `p>130c`; they do not falsify the conditional top classification. |
| `p=30000001` short Q/S non-top witnesses | Lie below `sqrt(2^57)` and therefore in the small range, not in the top exclusion. |
| `p=2` | Present in every positive central binomial coefficient. |
| `p=3` | Exactly handled by the forbidden least base-3 digit of `(RS-1)/2`. |
| `p=41,43` | Divide no branch because all slopes vanish and all constants are units modulo these primes. |
| `r=0` in the higher-power block definition | Admitted explicitly; the coarse block bound remains valid and the depth tends to infinity for each fixed `(p,a)`. |
| `X<p^a<=C0X` | Counted by the terminal prime-power bound, not omitted from dominated convergence. |
| `p=sqrt X` and `p=Y` | Assigned respectively to the small and transition ranges. |

No falsification witness crosses the actual hypotheses of a lemma used by
the new proof.

## 6. Reproduction commands

The new independent verifier and its exact tests:

```text
python3 compute730/full_density/verify.py
python3 -m pytest compute730/full_density/test_verify.py -q
```

The complete legacy falsification and repair suite must also remain green:

```text
python3 -m pytest compute730/campaign_uniform compute730/full_density/test_verify.py -q
```

Reproduction on 2026-07-13:

```text
........................................................................ [ 60%]
...............................................                          [100%]
119 passed in 13.26s
```

The standalone verifier printed:

```text
SOURCE_SHA256=3df2e48ca62e35dbfbd25406badf37574d910efb2ab39360ab3458f3a31c4292
T=5289
SLOPES={'P': 222138, 'Q': 380808, 'R': 148092, 'S': 380808}
CRT={'P': {'modulus': 222138, 'phi': 60480, 'allowed': 20160},
     'R': {'modulus': 148092, 'phi': 40320, 'allowed': 13440}}
S_UPPER=11117760449158646497/89848527388139520000
LOG2_UPPER=1123/1620
TOTAL_UPPER=21498408212212214497/22462131847034880000
POSITIVE_MARGIN=2344391769572639/22462131847034880000
```

The current exact verifier contains no floating-point operation.  The legacy
tests use floating point only in explicitly diagnostic paths; their hostile
verdicts and the imported witness checked here use integers and `Fraction`.

## 7. Kernel closure

All intake gates now pass:

```text
paper proof relative to Kummer + Mertens + fixed-modulus PNT-AP: PASS
finite exact certificates:                                      PASS
unconditional Lean positive-density theorem:                    PASS
unconditional Lean Erdős #730 infinitude theorem:               PASS
```

The former reduction hypothesis
`Erdos730.FullDensityReduction.CandidatePositiveDensityClaim` is discharged
by `Erdos730.FullDensityTheorem.candidatePositiveDensity`.  The exact terminal
declaration is

```text
Erdos730.FullDensityTheorem.pairSet_infinite :
  Erdos730.FullDensityCore.PairSet.Infinite
```

The dependency cone includes the local reciprocal-prime Mertens proof and the
fixed-modulus PNT-AP theorem imported from the axiom-clean external cone.  The
package's unrelated admitted experiments remain outside that cone.  The
kernel gate reports no `sorryAx` and no axiom beyond
`[propext, Classical.choice, Quot.sound]`.
