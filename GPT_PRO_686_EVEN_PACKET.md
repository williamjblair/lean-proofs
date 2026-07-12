# GPT Pro research packet: Erdős 686, uniform even rows

Snapshot: 2026-07-12

> **POSTSCRIPT (same-day intake).**  This outbound packet is now historical.
> Its row list predates the ordinary-kernel closures of `k=28` and `k=32`.
> The returned large-prime-component argument has also been strengthened and
> kernel-checked in `Erdos686LargePrimeGapComponent.lean`: any hypothetical
> large-row solution with prime `p≥k`, exponent `e>0`, and `p^e∣d` must
> satisfy
> `6*p^(2*e) < (13*k-6)*d + 18*(k-1)`.  The cited `d=k` and `d=k+1`
> branches remain paper-only because their external theorems are not
> formalized in this repository.  Use `FRONTIER.md` and
> `Erdos686FinalResidual.lean` for the live handoff.

## Purpose and return discipline

This is a self-contained research packet for one task: turn the existing
row-specific exact covers into a uniform proof for every even block length.
It deliberately omits the odd-tail/Farey lane and all generated Lean shards.

The desired theorem is

```text
For every even k >= 16 and n,d in N with d >= k,

    product_{i=1}^k (n+d+i) != 4 product_{i=1}^k (n+i).
```

Return only one of the following:

1. a complete, self-contained proof of that theorem; or
2. a complete proof for a genuine infinite subclass, such as all even
   `k >= K` or all even `k` in explicit infinite congruence classes, followed
   by one exact quantified statement of what remains.

Another isolated row, a search report, an unproved cover-existence lemma, or
a restatement of the target is not progress. Every asymptotic phrase must be
replaced by an explicit bound. Every external theorem must be quoted exactly
with its hypotheses checked. Every computation must use exact arithmetic and
be independently reproducible.

The eventual Lean proof must use no theorem axioms beyond
`[propext, Classical.choice, Quot.sound]`. `native_decide`, `sorry`, `admit`,
and custom theorem axioms are forbidden.

## Exact notation and current residual

The block product is

```lean
def blockProduct (k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (x + i)
```

The full residual is not asserted. Its large-row arm says that a hypothetical
equation outside the four closed rows must lie in the following domain:

```lean
16 ≤ k ∧ k ≤ d ∧
k ≠ 16 ∧ k ≠ 18 ∧ k ≠ 20 ∧ k ≠ 24 ∧
1218443 * k * d < 1853952 * n ∧
(∀ r : ℕ, ∀ hr : 2 ≤ r, k = 2 * r →
  d < max (2 * r)
    (universalEvenTailCoefficientCertificate r hr).threshold) ∧
(∀ p i A : ℕ, p.Prime → i ∈ Finset.Icc 1 k →
  (k - 1).factorial.factorization p ≤
    (4 : ℕ).factorization p +
      (localBlockCoefficientNat k i).factorization p →
  n + i ≠ p ^ A) ∧
(∀ p i A a : ℕ, p.Prime → k < p →
  i ∈ Finset.Icc 1 k → 1 ≤ A →
  3707904 * a ≤ 1218443 * k →
  n + i ≠ a * p ^ A)
```

Here

```lean
localBlockCoefficientNat k i = (i - 1)! * (k - i)!.
```

For this packet, additionally assume `k` is even. The goal is to contradict
the displayed domain uniformly, not to assume the residual contradiction.

## Kernel-banked inputs

The following statements have direct Lean proofs whose reported axiom sets
are contained in `[propext, Classical.choice, Quot.sound]`.

### Four completely closed rows

```lean
theorem no_gap_solution_four_even_sixteen {n d : ℕ} (hd : 16 ≤ d) :
  blockProduct 16 (n + d) ≠ 4 * blockProduct 16 n

theorem no_gap_solution_four_even_eighteen {n d : ℕ} (hd : 18 ≤ d) :
  blockProduct 18 (n + d) ≠ 4 * blockProduct 18 n

theorem no_gap_solution_four_even_twenty {n d : ℕ} (hd : 20 ≤ d) :
  blockProduct 20 (n + d) ≠ 4 * blockProduct 20 n

theorem no_gap_solution_four_even_twentyfour {n d : ℕ} (hd : 24 ≤ d) :
  blockProduct 24 (n + d) ≠ 4 * blockProduct 24 n
```

These are unconditional: they do not assume smoothness or an external
number-theory theorem.

### Universal effective tail for every even row

For every `r >= 2`, Lean constructs an explicit
`EvenTailCoefficientCertificate r`. It contains integral polynomials
`S,T,D`, integers `C,L,A,E,F`, a degree `q < r`, and a natural-number
threshold, with

```text
T^2 = C^2 S + D,
deg T <= r,
deg D <= q < r,
leading(T) = C > 0,
leading(D) = L != 0.
```

The threshold is constructed exactly as

```text
M = max(2r, max(2*|A|+1, max(7*|F|+1, 10*|E|+1))).
```

The equation-facing theorem is

```lean
theorem no_even_tail_solution_universal
    {r n d : ℕ} (hr : 2 ≤ r)
    (hd : max (2 * r)
      (universalEvenTailCoefficientCertificate r hr).threshold ≤ d) :
    blockProduct (2 * r) (n + d) ≠
      4 * blockProduct (2 * r) n
```

Thus every even row has only a finite strip in `d`, but this is not a finite
total computation because `r` is unbounded.

### Sharp centered ratio and large-prime owner band

Every exact quotient-four solution with `k >= 16` and `d >= k` satisfies

```lean
1218443 * k * d < 1853952 * n.
```

This is the strongest coefficient proved by the fixed `3621/2500` centered
root bracket. The cleaner weaker consequence is `23*k*d < 35*n`.

Consequently, if a lower term has the form

```text
n+i = a*p^A,
p prime, p > k, 1 <= i <= k, A >= 1,
3707904*a <= 1218443*k,
```

then the block equation is impossible. This is an exclusion theorem, not a
theorem supplying such an owner.

### Exact prime-power exclusion

If `n+i=p^A` and

```text
v_p((k-1)!) <= v_p(4) + v_p((i-1)! (k-i)!),
```

then the equation is impossible. In particular, every pure prime-power lower
term with base `p>k` is excluded. The criterion is not valid for every
interior power of `2` or `3`; counterfixtures appear below.

## Common centered square-root mechanism

Let `k=2r` and define

```text
v = 2n+k+1,
w = 2(n+d)+k+1 = v+2d,

S_r(W) = product_{j=1}^r (W^2-(2j-1)^2).
```

The original block equation is exactly

```text
S_r(w) = 4 S_r(v).
```

Write

```text
S_r(W) = W^(2r) + s_1 W^(2r-2) + ... + s_r.
```

The polynomial part of its formal square root is obtained recursively. Set
`u_0=1` and, for `j>=1`,

```text
2*u_j + sum_{h=1}^{j-1} u_h*u_(j-h) = s_j.
```

Retain the terms with nonnegative exponent in

```text
Q_r(W) = sum_j u_j W^(r-2j).
```

Choose the least convenient positive integer `C_r` clearing denominators,
put `T_r=C_r Q_r`, and define

```text
D_r(W) = T_r(W)^2 - C_r^2 S_r(W).
```

For a hypothetical solution, set

```text
m = T_r(w)-2T_r(v),
X = T_r(w)+2T_r(v).
```

Then

```text
m*X = D_r(w)-4D_r(v).                         (1)
```

Let `F_r` be the exact fixed divisor of `T_r` on odd integers. Since `v,w`
are odd, `F_r | m`. Archimedean coefficient certificates trap `m` in a
finite interval; write `m=-F_r*t`.

For a prime `p` not dividing `F_r`, define the exact local set

```text
A_p(r) = {
  (-F_r)^(-1) * (T_r(w)-2T_r(v)) mod p :
  v,w in F_p and S_r(w)=4S_r(v)
}.
```

Every integer solution forces

```text
t mod p in A_p(r).                             (2)
```

The existing row closures select primes for which the intersection of (2)
contains no integer in the trapped interval. The open question is whether
the existence of such a cover has a structural proof uniform in `r`.

## Exact row data

### Row `k=16`

Here the fixed divisor is `F_16=16384`. Exact shifted inequalities prove

```text
-16384 < m < 0,
16384 | m,
```

so there is no nonzero candidate. No prime-field cover is needed.

This simple one-step mechanism already fails at `k=18` and generally cannot
serve as the uniform argument.

### Row `k=18`: fully kernel checked

The exact polynomial part and deficit are

```text
T(W) = 128W^9 - 62016W^7 + 9038832W^5
       - 439659848W^3 + 3788405307W,

D(W) = 78397083729792W^8 - 16673477276146464W^6
       + 945705074655002832W^4 - 9110023357135451751W^2
       + 19455213098280960000.
```

The exact odd fixed divisor is `F_18=81`.

For `18 <= d <= 55`, exact ratio bounds leave

```text
12d-17 <= n <= floor((25d-3)/2).
```

There are 1,311 pairs, and none satisfies the centered product equation.
The smallest absolute error is

```text
2307600880601197152466465133764408497930240000
```

at `(d,n)=(19,228)`.

For `d>=56`, shifted-coefficient certificates prove

```text
-242269137 < m < 0,
81 | m.
```

Thus `m=-81t` with `1<=t<=2990976`. A compact exact-arithmetic 35-prime
cover is

```text
primes:
19, 907, 827, 941, 887, 857, 991, 919, 967, 911, 883, 947,
839, 997, 821, 751, 769, 547, 859, 659, 977, 797, 491, 811,
757, 809, 509, 619, 281, 677, 773, 431, 593, 487, 163

survivor counts, including the initial and terminal counts:
2990976, 629678, 433898, 299046, 209294, 147358,
104870, 74591, 53653, 38716, 27980, 20257, 14697,
10744, 7859, 5763, 4222, 3076, 2244, 1627, 1194,
855, 610, 443, 317, 227, 156, 108, 75, 49, 33, 19,
11, 4, 1, 0.
```

The Lean implementation uses a different 62-prime order with maximum prime
857 to lower peak kernel memory. It has 190 bounded field shards, 77 balanced
quotient scans, seven group glues, and a top cover. Its final counts are
`...,5,4,3,2,1,0`. The public row theorem reports only the permitted axioms.

Important obstruction: the earlier weaker trap left `1<=t<=9036292`.
Applying every prime through 1000 left exactly

```text
t=2990977 and t=3541067.
```

Both have a local pair `(w,v)` for every tested prime through 5000. The
second-stage Archimedean improvement to `t<=2990976`, rather than more
distinct prime fields, is what removes them.

### Row `k=20`: fully kernel checked

Exact inequalities give

```text
-5853806 < m < 0,
3200 | m,
1 <= t <= 1829.
```

The cover is

```text
primes:          227, 199, 233, 239, 211, 197, 241
survivor counts: 1829, 811, 355, 165, 73, 26, 9, 0.
```

### Row `k=24`: fully kernel checked

Exact inequalities give

```text
-5993518490 < m < 0,
10616832 | m,
1 <= t <= 564.
```

The cover is

```text
primes:          13, 191, 157, 227, 239, 241, 131, 197, 71
survivor counts: 564, 304, 170, 96, 51, 26, 11, 5, 1, 0.
```

### Row `k=32`: exact arithmetic complete, Lean gate pending at snapshot

For `r=16`, the recurrence above gives integral `T`, scale `C=1`,
`deg S=32`, `deg T=16`, and `deg D=14`. The exact odd fixed divisor is

```text
F_32 = 3221225472 = 3*2^30.
```

The exact verifier uses

```text
4*22^32 < 23^32,
49^32 < 4*47^32,
4*45^32 < 47^32.
```

It checks the finite strip `32<=d<=127` directly. The ratio window contains
exactly 14,352 `(d,n)` pairs, and none is a solution.

For `d>=128`, take

```text
v0=5603,
w0=5859,
TRAP=1388955148309984.
```

All 153 shifted coefficients for the lower trap are positive, and the exact
upper sign certificate has 15 positive shifted coefficients. Consequently
`m=-F_32*t` with

```text
1 <= t <= floor((TRAP-1)/F_32) = 431188.
```

The deterministic greedy cover over primes at most 521 is

```text
primes:
17, 521, 509, 491, 457, 463, 487, 383, 449,
439, 499, 443, 7, 431, 397, 467, 409

survivor counts, including the initial and terminal counts:
431188, 177548, 86232, 42235, 21029, 10678, 5404, 2769,
1444, 743, 375, 179, 89, 47, 23, 10, 4, 0.
```

The first prime leaves exactly

```text
t mod 17 in {0,3,6,7,10,13,14}.
```

Writing `t=17q+r` reduces the final Boolean scan to `q<25365`.

The Python verifier independently reconstructs `S,T,D`, proves the exact
fixed divisor from 17 consecutive odd values, checks both shifted
coefficient certificates, checks all 14,352 finite-strip pairs, reconstructs
every field mask, and replays the survivor sequence to zero.

At this snapshot, generated ordinary-kernel tables were still building and
the top-level `Erdos686EvenK32.olean` did not yet exist. Treat `k=32` as an
exact-computation result, not a kernel-banked theorem, until a fresh direct
Lean run prints only `[propext, Classical.choice, Quot.sound]`.

## Cross-row data and the actual uniformity problem

The square-root mechanism was reconstructed exactly for every even
`16<=k<=100`. If `k=2r`, the observed and algebraically verified deficit
degrees are

```text
deg D = r-2 when r is even,
deg D = r-1 when r is odd.
```

The exact fixed divisor of `T(2z+1)` is the gcd of any `r+1` consecutive
values; finite differences prove this is the full fixed divisor.

Representative boundary data are

| k | integral scale C | odd fixed divisor F | first admissible odd center | one-step trap |
|---:|---:|---:|---:|:---|
| 16 | 1 | 16384 | 355 | below F |
| 18 | 128 | 81 | 451 | above F |
| 20 | 1 | 3200 | 559 | above F |
| 24 | 1 | 10616832 | 809 | above F |
| 32 | 1 | 3221225472 | 1447 | above F |
| 50 | 4194304 | 15625 | 3559 | above F |
| 100 | 1 | 589824000000000000 | 14329 | above F |

Therefore, the direct `-F<m<0` argument is exceptional to `k=16`. A uniform
proof must explain why a modular cover exists, replace the covers with a
global reciprocity/product obstruction, or derive a different owner theorem.

Questions that need proof rather than experiment:

1. Is there a parametric family of primes whose local density product is
   small enough, together with a deterministic theorem eliminating every
   trapped `t`?
2. Are the observed covers shadows of quadratic nonresidue incompatibility,
   reciprocity, a resultant, or a primitive-divisor theorem?
3. Can the exact equation force a lower owner `a*p^A` inside the banked band
   `3707904a<=1218443k`?
4. Can the universal tail threshold itself be combined with a uniform bound
   on the number of possible fixed-divisor multiples?
5. Is there a structural distinction between the `r` even and `r` odd
   deficit degrees that yields infinite subclasses?

## Mandatory falsification record

Any proposed proof must survive these facts.

1. **Finite per row is not finite uniformly.** The universal even-tail
   theorem leaves a finite strip for each `r`, but `r` is unbounded.
2. **A terminating search is not yet proved.** An algorithm that searches
   for primes until a cover appears does not prove that it terminates for
   every `r`.
3. **The one-step fixed-divisor trap fails.** It already fails at `k=18` and
   at the sampled rows through 100.
4. **Distinct prime fields alone did not remove the first `k=18` global
   survivors.** The Archimedean trap had to be sharpened below the first
   survivor.
5. **No owner-supply theorem is banked.** The sharp cofactor theorem only
   excludes an owner after its existence and size have been proved.
6. **Interior prime powers are not uniformly excluded.** Exact fixtures
   `(A,k,d,i,n)=(9,33,33,2,510)` for `p=2` and
   `(5,16,19,8,235)` for `p=3` fail the split-factorial premise. They are
   falsifiers of an unrestricted interior-prime-power claim, not asserted
   block equations.
7. **Power windows do not certify a `7/10` ratio.** The non-equation point
   `(k,n,d)=(16,175,16)` satisfies the three recorded power windows while
   `10n<=7kd`. Any stronger ratio needs new equation structure.
8. **Row-specific covers are not an induction.** No theorem currently maps a
   cover for `k` to a cover for `k+2`.

## Exact reproduction commands

From the repository root:

```bash
# Banked theorem surfaces
lake env lean ErdosProblems/Erdos686EvenK18.lean
lake env lean ErdosProblems/Erdos686CenteredRatioWindowSharp.lean
lake env lean ErdosProblems/Erdos686EvenTailSupply.lean

# k=18 independent exact reproduction
python3 compute/campaign686/agent_t2_even_uniform_sqrt/even_uniform_sqrt_verify.py
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k18_archimedean_closure_verify.py
python3 -m pytest -q \
  compute/campaign686/agent_t2_even_uniform_sqrt

# k=32 independent exact reproduction
python3 compute/campaign686/agent_t2_even_k32/even_k32_verify.py
python3 -m pytest -q compute/campaign686/agent_t2_even_k32

# k=32 kernel gate once generation/build has completed
lake env lean ErdosProblems/Erdos686EvenK32.lean
```

## Source hashes at this snapshot

```text
c513a79ac8cf03a4c566ab0dd2a3083f3ae708d71b4d0da13a67ff8b2615817c  ErdosProblems/Erdos686FinalResidual.lean
43328f2159ea1eec247dc55077323a5aa335abd45c00ae5579ee589e57cf8e4a  ErdosProblems/Erdos686CenteredRatioWindowSharp.lean
7784331341c8c8eff14a2c27d7a344e8a130ce6c4f569178bd42a74c1aa54da5  ErdosProblems/Erdos686EvenTailSupply.lean
c91c1933e9d5fb2dc80eafec3def9ba6bd57cb7d7d0070ee14ca492ed5a3d52d  ErdosProblems/Erdos686EvenK18.lean
870c1a3d31c928cf08bc6a2c5a9590183e7c5fdf1c6300db3be9a846651fd5ce  compute/campaign686/agent_t2_even_uniform_sqrt/even_uniform_sqrt_verify.py
6d445e06c876cccbaaaad4bbc44550f29649d290e03eb38a69d8368e44bfb5c4  compute/campaign686/agent_t2_even_k32/even_k32_verify.py
6948444282e1c5ac91037bf3c7a0f13c5d8216383dab3c3b10726bfb0f1d2def  compute/campaign686/agent_t2_even_k32/even_k32_cover_search.py
6dbbc24ad333359e01e40de60274bdf5deda94008b5d2f67385c35a53cff0b1f  ErdosProblems/Erdos686EvenK32CandidateDefs.lean
722a6adea48661828a77f9e44da49a18921ac8b2b7001246cc7f7e509dcca75a  ErdosProblems/Erdos686EvenK32CandidateCover.lean
```

## Instructions to the independent researcher

Reverse-engineer the common algebraic content of the exact covers. Separate
incidental greedy prime choices from properties forced by `S_r`, `T_r`, and
`F_r`. Seek a parametric cover, a reciprocity/resultant replacement, a
primitive-divisor argument, or an owner-supply theorem.

For any proposed uniform cover, provide:

- an explicit prime-selection rule;
- a proof that the required primes exist;
- explicit bounds on their number and size;
- a proof that every trapped integer is eliminated;
- a proof uniform in `r`, including the first applicable row;
- exact reproduction code for every finite calculation.

End with a dependency tree and assign every node exactly one status:
`PROVED`, `EXACT COMPUTATION`, `PUBLISHED THEOREM CHECKED`, or `OPEN`.
Hostile-audit the argument against every item in the mandatory falsification
record before claiming closure.
