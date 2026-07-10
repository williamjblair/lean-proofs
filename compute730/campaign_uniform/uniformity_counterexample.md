# Counterexample to the stated uniform incomplete-block lemma

Date: 2026-07-10

Verdict: **the uniform lemma in `codex/prompt_730_uniform_lemma.md` and
`compute730/audit.md` is false as stated.**  The failure persists for
intervals of length `p^r` times any fixed polylogarithm and persists if the
exact-valuation condition `p` does not divide `c(k)` is imposed.

This is a counterexample to the missing analytic lemma, not a counterexample
to Erdős #730 and not a proof that the surrounding family cannot be repaired.

The audit names scratchpad diagnostics `check1_kummer.py`,
`check2_family.py`, and `check3_survivors.py`, but those files are not present
in this worktree or the searched local Codex/personal directories.  The
accompanying evaluator reconstructs the maps directly from the audited
formulas rather than relying on those unavailable scripts.

## 1. Exact maps and quantifiers

Put

```text
T = 5289,
A = 3024 T^2 = 84,591,927,504.
```

For a branch `L(x)=lambda_L x+mu_L`, a prime `p` for which the branch has an
admissible root, and `a>=1`, choose the least root

```text
x0 = -mu_L lambda_L^(-1) mod p^a,
c0 = L(x0)/p^a.
```

Writing `x=x0+p^a k` gives `c=L(x)/p^a=c0+lambda_L k`.  Direct expansion of
the four audited Phi maps gives

```text
G(k) = A p^a k^2 + (p^a u_L+b_L)k+v_L,
v_L = Phi_L(c0).
```

The exact data are:

| branch | `lambda_L, mu_L` | `Phi_L(c)` | `u_L` | `b_L` |
|---|---|---|---|---|
| P | `42T, 11` | `(12p^a c^2-41c)/7` | `144T c0` | `-246T` |
| Q | `72T, 13` | `(7p^a c^2+41c)/12` | `84T c0` | `246T` |
| R | `28T, 5` | `(54p^a c^2+129c-7)/14` | `216T c0` | `258T` |
| S | `72T, 19` | `(7p^a c^2-43c-6)/12` | `84T c0` | `-258T` |

Thus

```text
b_P=-1,301,094, b_Q=1,301,094,
b_R= 1,364,562, b_S=-1,364,562.
```

For `p` outside `{2,3,41,43}` and an admissible branch, `p` does not divide
`b_L`.  At `p=7`, P and R have no root because their slopes are divisible by
7 while their intercepts are not; Q and S are the admissible branches.

Let

```text
D_(p,m) = {sum_(i=0)^(m-1) d_i p^i : 0<=d_i<=(p-1)/2}.
```

The claimed bound, with `H=(p+1)/2`, is

```text
#{k in I : G(k) mod p^(2r) belongs to D_(p,2r)}
  <= (H/p)^(2r) |I| (1+o(1))
```

for every `a`, every admissible root, and every interval of length at least
`p^r polylog(p^r)`.  If `a` denotes an exact valuation, one additionally
retains only `k` with `p` not dividing `c0+lambda_L k`.

## 2. Affine degeneration

Fix any one of `p=5,7,11` and use the Q branch.  Its slope and `b_Q` are
units modulo all three primes.  For each `r`, take

```text
a=2r, q=p^(2r), b=b_Q>0.
```

Modulo `q`, both terms containing `p^a` vanish, so

```text
G(k) = bk+v (mod q).
```

Because `b` is a unit modulo `q`, for any residue `rho` we may choose `k0`
with

```text
bk0+v = rho (mod q).
```

Then for every integer `j`,

```text
G(k0+j) = rho+bj (mod q).                                  (1)
```

This exact affine degeneration is the obstruction.  It occurs before any
incomplete quadratic-sum estimate can be applied.

### A stronger near-affine counterexample band

The failure is not confined to `a>=2r`.  For every `a>=1`, put

```text
s=max(2r-a,0).
```

For every `k0,t`, exact subtraction gives

```text
G(k0+t)-G(k0)-bt
  = p^a t (A(2k0+t)+u_L).                                  (1a)
```

Consequently, whenever `p^s | t`, the right side vanishes modulo
`p^(2r)`: when `a<2r`, one has `a+s=2r`; when `a>=2r`, the factor `p^a`
already vanishes.  In the pigeonhole argument below, partitioning outputs
modulo

```text
b p^max(s,1)
```

forces the needed divisibility and also keeps the exact valuation constant
modulo `p`.

This gives a lower bound of fixed-constant size

```text
H^r/(b p^max(s,1))
```

against a claimed main term of size

```text
H^(2r) p^(-r) poly(r).
```

Their ratio is, up to fixed and polynomial factors (including the extra
fixed factor `p` when `s=0`),

```text
(p/H)^r p^(-s).
```

The precise divergence criterion supplied by the construction is

```text
(p/H)^r p^(-s) / poly(r) -> infinity.                       (1b)
```

Thus the claimed uniformity fails for every sequence with

```text
limsup_(r to infinity) s/r < kappa_p,
kappa_p = log_p(p/H).
```

For the diagnostic primes,

```text
kappa_5  = 0.3173938055,
kappa_7  = 0.2875856258,
kappa_11 = 0.2527782637.
```

Equivalently, for every fixed `epsilon>0`, it fails throughout

```text
s <= (kappa_p-epsilon)r
```

for all sufficiently large `r`.  In particular, `a=2r-1` is still in the
counterexample range.  Merely changing the proposed lemma to `a<2r` would
not repair it.

## 3. Many restricted multiples of b

Let

```text
S_r = {0<=y<p^r : all r base-p digits of y are in {0,...,H-1}}.
```

Thus `|S_r|=H^r`.

First retain the exact valuation.  Modulo `p`, the affine output determines
the parameter:

```text
k = b^(-1)(G(k)-v) (mod p).
```

Since `lambda_Q` is also a unit, the condition

```text
p divides c0+lambda_Q k
```

corresponds to exactly one forbidden output residue `d_bad mod p`.  Remove
from `S_r` the numbers whose least digit is `d_bad` if that digit is in the
restricted alphabet.  The remaining set `S_r*` satisfies

```text
|S_r*| >= (H-1) H^(r-1).                                   (2)
```

Partition `S_r*` by residue modulo `bp`.  By pigeonhole, some class `rho`
contains a subset `Y_r` with

```text
|Y_r| >= (H-1) H^(r-1)/(bp).                               (3)
```

Choose `k0` in (1) for this `rho`.  For each `y` in `Y_r`, put

```text
j = (y-rho)/b.
```

This is an integer because `y=rho (mod bp)`, and in fact `j=0 (mod p)`.
Equation (1) gives

```text
G(k0+j) = y (mod q).                                       (4)
```

All these parameters retain the exact valuation, since their differences
from `k0` are multiples of `p` and `rho mod p` was not the forbidden output
residue.  Moreover

```text
max_(y in Y_r) j - min_(y in Y_r) j < p^r/b < p^r.          (5)
```

Fix any proposed polylog exponent `C>=0`, set

```text
N_r = ceil(p^r (log p^r)^C),
```

and take an interval of length `N_r` beginning at
`k0+min_(y in Y_r) j`.  By (5), it contains every parameter constructed
above.  If nonnegative parameters are required, add a sufficiently large
multiple of `q` to `k0`; this changes neither (1) nor the exact valuation.

For every hit, (4) lies in `[0,p^r)`.  Its lower `r` digits are restricted
and its upper `r` digits are all zero.  Therefore the interval contains at
least the count in (3) valid hits.

This argument is exact and combinatorial.  It does not require an
equidistribution theorem for restricted digits modulo `b`.

## 4. Contradiction to every fixed-polylog bound

The claimed main term on `I_r` is

```text
(H/p)^(2r) N_r = O((H^2/p)^r (r log p)^C).
```

Dividing the lower bound (3) by this quantity gives, up to a fixed constant,

```text
(p/H)^r / (r log p)^C.
```

But

```text
p/H = 2p/(p+1) > 1.
```

The ratio tends to infinity exponentially.  Therefore no choice of fixed
polylog exponent, no explicit `o(1)`, and no larger fixed multiplicative
constant can make the stated uniform inequality true.

## 5. Exact p=5,7,11 diagnostics

The accompanying `test_uniformity.py` reconstructs every admissible map,
checks its expanded coefficients and permutation property, and scans every
interval start modulo `p^(2r)` on the Q branch.  Even at the bare critical
length `|I|=p^r`, the exact-valuation count exceeds the concrete advertised
factor `1+1/log(p^r)` in these examples:

| p | r | a | interval | exact hits | advertised RHS |
|---:|---:|---:|---|---:|---:|
| 5 | 2 | 4 | `[137,162)` | 6 | 4.2466 |
| 7 | 3 | 6 | `[16138,16481)` | 16 | 13.9873 |
| 11 | 2 | 4 | `[1461,1582)` | 14 | 12.9441 |

The last column is a floating-point diagnostic because it contains a
logarithm.  The pytest suite uses only exact integer inequalities against the
main term: after clearing the denominator `p^(2r)`, it checks

```text
exact_hits * p^(2r) > H^(2r) * |I|.
```

These small examples diagnose the same translated-window bias.  The proof
in §§2--4 is what refutes the stated lemma with its arbitrary fixed
polylogarithmic minimum length.

## 6. Consequence for sparse Fourier completion

Sparse Fourier completion cannot prove the requested statement: at `a=2r`
the quadratic phase has disappeared modulo the digit modulus, and throughout
the near-affine band above it is constant on a sufficiently sparse parameter
progression.  The count is genuinely larger than the asserted density.  A
viable repair must split off that whole band and exploit the rarity of high
valuations in the global first moment, or weaken interval uniformity.  The
first option is now implemented for maximal admissible `r`: the companion
`repair/near_affine_payment_findings.md` proves a normalized cost below
`0.01` for `X>=2^57`.  The complementary separated range remains the
sparse-Fourier target, and no estimate for it is proved here.
