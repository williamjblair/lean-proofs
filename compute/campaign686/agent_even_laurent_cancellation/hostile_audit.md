# Hostile audit: Laurent-term cancellation beyond the even polynomial part

## Verdict

**Exact structural falsifier; no row is closed.**

For `r in {11,13,15,17}` (`k=22,26,30,34`), the verifier constructs:

1. the canonical polynomial part of `sqrt(S_r)`;
2. the rational approximant obtained by adjoining the first negative Laurent
   term;
3. the first four canonical even-denominator Padé approximants; and
4. the exact integer eliminants and their maximal fixed divisors on odd
   centers.

Every tested corrected deficit still has degree exactly `r-1`. Thus
cross-multiplication restores the same one-power center decay as the
canonical Runge construction; it does not gain a new exponent. At the exact
first gap beyond `18d <= k^2`, the ordinary fixed-divisor trap succeeds on
zero of the 108 possible power-window center pairs. The stronger congruence
retained by the first negative term also succeeds on zero of those 108 pairs.

This rules out the tested Laurent/Padé bridge. It does not rule out all
rational approximants, a defective higher Padé denominator, or a new
equation-specific owner correlation.

## Exact setup

For odd `r=2s+1`, put

```text
S_r(x) = product_{j=1}^r (x^2-(2j-1)^2)
sqrt(S_r(x)) = x^r * sum_{n>=0} c_n x^(-2n).
```

The coefficients are defined without analysis by

```text
c_0 = 1,
2c_n + sum_{i=1}^{n-1} c_i c_(n-i) = [z^n] product_j(1-(2j-1)^2 z).
```

The canonical polynomial part is

```text
Q_r(x) = sum_{n=0}^s c_n x^(r-2n).
```

After minimal positive denominator clearing, write `T=CQ_r` and
`D=T^2-C^2S_r`. The four exact leading datasets are:

| `r` | `k` | `C` | `deg D` | `[x^(r-1)]D` | fixed divisor of `T(2a+1)` |
|---:|---:|---:|---:|---:|---:|
| 11 | 22 | 256 | 10 | 463278576995462272 | 33 |
| 13 | 26 | 1024 | 12 | 15964983062123304268800 | 13 |
| 15 | 30 | 2048 | 14 | 188913625945385407495200000 | 30375 |
| 17 | 34 | 32768 | 16 | 188162318421570695167361039564800 | 255 |

The `r=17` row exactly reproduces the canonical data and fixed divisor used
by the quadratic-tail hostile audit.

## First negative Laurent term

Write

```text
sqrt(S_r(x)) = Q_r(x) + b_r/x + e_r/x^3 + O(x^-5).
```

The corrected rational approximant is

```text
P_1(x)/B_1(x) = (xQ_r(x)+b_r)/x.
```

After primitive simultaneous denominator clearing, define

```text
H_1 = P_1^2-B_1^2 S_r.
```

The recurrence proves the exact leading identity

```text
[x^(r-1)]H_1 = -2 C_1^2 e_r.
```

In every requested row `e_r` is nonzero, so `deg H_1=r-1`. The exact data
are:

| `r` | `b_r` | primitive scale `C_1` | fixed divisor `G_1` of the eliminant | `[x^(r-1)]H_1` | optimistic leading-only center `floor(10 abs(Hlead)/G_1)+1` |
|---:|:---|---:|---:|---:|---:|
| 11 | `-3619363882777049/1024` | 1024 | 11264 | 3100928273993976380416 | 2752954788702038691 |
| 13 | `-15590803771604789325/2048` | 2048 | 26624 | 38109964241278325795892480 | 14314139213220525013482 |
| 15 | `-737943851349161748028125/32768` | 32768 | 995328000 | 39036086887414397157127065600000 | 392193195483442615470751 |
| 17 | `-5742258252611410374980500475/65536` | 65536 | 5570560 | 789935870832632257303211827416498176 | 1418054685404397865390933456272 |

The last column is deliberately optimistic: it discards every lower
coefficient. Even this scale is far beyond the first-complement center in
each row. More importantly, the exact boundary audit below does not depend
on that coarse norm.

## Exact Padé degree obstruction

For order `m>=1`, the canonical even denominator is

```text
B_m(x)=x^(2m)+beta_1 x^(2m-2)+...+beta_m.
```

Choose the `beta_j` so that the first `m` negative coefficients of
`B_m sqrt(S_r)` vanish, and let `P_m` be its polynomial part. If the first
uncancelled coefficient is `rho_(r,m)`, then exactly

```text
B_m sqrt(S_r)-P_m = rho_(r,m) x^(-(2m+1)) + lower powers,
P_m^2-B_m^2 S_r = -2 rho_(r,m) x^(r-1) + lower powers.
```

After primitive scaling by `C_(r,m)`, the second leading coefficient becomes
`-2 C_(r,m)^2 rho_(r,m)`. Therefore any nonzero `rho_(r,m)` leaves deficit
degree exactly `r-1`, independent of `m`.

The verifier solves all coefficient systems over `Fraction` for

```text
r in {11,13,15,17},  1 <= m <= 4.
```

All sixteen systems are nonsingular and all sixteen `rho_(r,m)` are nonzero.
Consequently none of the denominator degrees `2,4,6,8` gains a decay power.
The complete rational denominator coefficients, primitive scales, fixed
divisors, leading deficits, and per-construction SHA-256 values are in the
canonical JSON payload.

For the first even denominator (`m=1`), the optimistic leading-only centers
are already:

| `r` | optimistic center |
|---:|---:|
| 11 | 181620781884765594970655395698575637238992 |
| 13 | 93565151987079387699665901991518019164096110425942251 |
| 15 | 183087105618759406561330087528013749853686713468834526 |
| 17 | 24521022192444038999255985983453551082818367819731348257165015592532747343229851 |

Denominator clearing overwhelms the available fixed divisor rather than
improving it.

## Integer eliminant and fixed divisor

For any primitive integral pair `P,B`, put `H=P^2-B^2S_r` and

```text
E(v,w) = B(v)P(w)-2B(w)P(v),
F(v,w) = B(v)P(w)+2B(w)P(v),
R(v,w) = B(v)^2 H(w)-4B(w)^2 H(v).
```

The exact polynomial identity is

```text
E*F = R + B(v)^2 B(w)^2 (S_r(w)-4S_r(v)).
```

Thus a hypothetical equation gives `E*F=R`. On odd centers, let `G` be the
fixed divisor of `E`. After substituting `v=2a+1,w=2b+1`, the degree in each
integer variable is at most `max(deg P,deg B)`. The gcd on the consecutive
square grid of side `max(deg P,deg B)+1` is therefore the exact fixed divisor
by the bivariate finite-difference basis. The verifier computes this grid and
checks an additional surrounding grid for every construction.

Whenever `F>0`, `R!=0`, and

```text
abs(R) < G*F,
```

the equation is impossible. This is the strongest contradiction obtainable
from the constant fixed divisor alone without further information about the
residue of `E/G`.

## Stronger variable congruence from the Laurent correction

The first-negative construction retains more information than its constant
fixed divisor. Let `L=[x^(r-1)]D` and let `g` be the fixed divisor of
`T(2a+1)`. Define

```text
U(x)=2C*x*T(x)-L,
H_U=U^2-(2C^2*x)^2 S_r,
E_U=vU(w)-2wU(v).
```

Since `T(w)-2T(v)` is divisible by `g`, exactly

```text
E_U = 2Cvw (T(w)-2T(v)) - L(v-2w),
E_U == -L(v-2w)  (mod 2Cgvw).
```

Let

```text
delta(v,w)=dist(L(v-2w), 2Cgvw*Z),
F_U=vU(w)+2wU(v),
R_U=v^2 H_U(w)-4w^2 H_U(v).
```

Under the equation, `E_U F_U=R_U`. Hence the strongest contradiction using
this complete congruence class alone is

```text
0 < abs(R_U) < delta(v,w)*F_U.
```

The audit tests this exact inequality, not a coefficient norm or an
asymptotic surrogate.

## Exact first-complement falsification

The necessary endpoint power windows at the first gap beyond the quadratic
strip are:

| `r` | `k` | `d` | `n` window | center `v` window | pairs |
|---:|---:|---:|:---:|:---:|---:|
| 11 | 22 | 27 | `394..414` | `811..851` | 21 |
| 13 | 26 | 38 | `668..692` | `1363..1411` | 25 |
| 15 | 30 | 51 | `1049..1077` | `2129..2185` | 29 |
| 17 | 34 | 65 | `1528..1560` | `3091..3155` | 33 |

Each endpoint is checked on both sides by exact integer powers. The `k=34`
window is exactly the mandatory `3091<=v<=3155` fixture from the prior
quadratic-tail audit.

Across all 108 pairs:

- the first-negative constant-fixed-divisor inequality succeeds `0` times;
- the stronger exact variable-congruence inequality succeeds `0` times;
- the `m=1` even-Padé fixed-divisor inequality succeeds `0` times;
- every conjugate factor `F` is positive; and
- every displayed Padé residual `R` is nonzero.

For reference, at the lower endpoint of each row the variable-congruence
failures are:

| `r` | `(n,v,w)` | exact `delta(v,w)` | `floor(abs(R_U)/(delta F_U))` |
|---:|:---:|---:|---:|
| 11 | `(394,811,865)` | 5888085632 | 49950796 |
| 13 | `(668,1363,1439)` | 2278441984 | 3669979500880 |
| 15 | `(1049,2129,2231)` | 275592132000000 | 304605842630 |
| 17 | `(1528,3091,3221)` | 69405637509120 | 1060887394302882920 |

These pairs are route falsifiers, not equation witnesses. The inequalities
fail before one asks whether `S_r(w)=4S_r(v)`.

## Mandatory fixture audit

- **Quadratic boundary:** every last covered and first complementary gap is
  checked by `18(d-1)<=k^2<18d`.
- **Power-window endpoints:** both failed predecessor/successor inequalities
  and both successful endpoint inequalities are checked with integer powers.
- **`k=34` live fixture:** `d=65` and `3091<=v<=3155` are reproduced exactly.
- **`k=22` unrestricted local fixtures:** the three signed root pairs

  ```text
  (t,w,v) =
  (28643526033,-3,-1),
  (19687413989,-7,-1),
  (3809308513,13,15)
  ```

  satisfy `S(w)=S(v)=0` and `T(w)-2T(v)=-33t` exactly. They remain outside
  the positive-center theorem domain and are not misreported as solutions.
- **Large campaign pseudo-witnesses:** no uniform large-`k` obstruction is
  claimed here, so the row-984 and census fixtures are outside the quantified
  surface rather than silently discarded.

## Dependency tree and verdicts

1. **Centered polynomial and Laurent recurrence** — PASS in exact arithmetic.
2. **Canonical denominator clearing and fixed divisors** — PASS; all four
   rows reproduce independently.
3. **First negative coefficient and one-pole identity** — PASS.
4. **Even Padé systems for orders 1 through 4** — PASS; sixteen nonsingular
   systems and sixteen nonzero remainder coefficients.
5. **Degree gain beyond `r-1`** — FAIL for every tested construction.
6. **Bivariate odd-center fixed divisors** — PASS in exact arithmetic via the
   finite grid bound.
7. **Cross-multiplied eliminant identity** — PASS at every tested pair.
8. **Constant fixed-divisor boundary trap** — FAIL on all 108 pairs for the
   first-negative term and all 108 for the first even Padé denominator.
9. **Full variable-congruence boundary trap** — FAIL on all 108 pairs.
10. **Lean theorem or row closure** — NOT PRESENT.

## Scope and exact remaining opportunity

The negative result is deliberately limited to:

```text
r in {11,13,15,17},
the first negative Laurent term,
canonical even Padé orders 1<=m<=4,
the constant fixed divisor of E,
and the complete congruence E_U == -L(v-2w) mod 2Cgvw.
```

It does not prove that every higher Padé remainder is nonzero. The precise
algebraic condition for a higher canonical denominator to gain a decay power
is a Padé defect:

```text
rho_(r,m)=0,
```

equivalently `deg(P_m^2-B_m^2S_r)<=r-3` in these parity rows. No such defect
occurs for `1<=m<=4`. Even a defect would still need a new lattice estimate.

Without a defect, a successful continuation must add equation-specific
owner information that gives a lower bound stronger than the exact distance

```text
delta(v,w)=dist(L(v-2w),2Cgvw*Z).
```

Merely restating that this distance beats `abs(R_U)/F_U` on hypothetical
solutions would be theorem-strength and is not counted as progress here.

## Kernel status

This artifact is exact Python evidence only. It adds no Lean declaration and
makes no axiom-gate claim. A formal version would need:

1. the Laurent recurrence and the leading-deficit formula;
2. the finite four-row coefficient certificates;
3. the bivariate fixed-divisor grid theorem; and
4. only after a genuinely successful inequality exists, the integer trap.

Since the decisive inequalities are false at the required boundary, no Lean
formalization is proposed.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_even_laurent_cancellation/even_laurent_cancellation_verify.py \
  --pretty

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_even_laurent_cancellation/test_even_laurent_cancellation_verify.py
```

Canonical payload SHA-256:

```text
6de2a507b30ea4e71398e6f9a5d8c10ac6b437d68318134cb14991d22637f41b
```
