# Target 2: exact square-root closures at `k = 16,18,20,24`

## Result

Four large even rows are now closed unconditionally in Lean:

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

The proofs are in `ErdosProblems/Erdos686EvenK16.lean`,
`ErdosProblems/Erdos686EvenK18.lean`, and
`ErdosProblems/Erdos686EvenK182024.lean`.  They assume neither smoothness nor
any external number-theory theorem.  They prove the corresponding instances
of Target 2 vacuously, by excluding the equation itself.

## Exact argument

For

```
S(W) = (W²-1)(W²-9)(W²-25)(W²-49)
       (W²-81)(W²-121)(W²-169)(W²-225),

T(W) = W⁸ - 340W⁶ + 31926W⁴ - 862580W² - 2167279,

D(W) = 2139095040W⁶ - 280506662912W⁴
       + 8679734640640W² + 588267913216,
```

direct expansion gives `T(W)²=S(W)+D(W)`.  If

```
v = 2n+17,       w = 2(n+d)+17,
```

then the block equation is exactly `S(w)=4S(v)`.  Hence, for

```
m = T(w)-2T(v),       X = T(w)+2T(v),
```

one has

```
mX = D(w)-4D(v).                                      (1)
```

The proof has three quantitative inputs.

1. The exact power bracket `4·11¹⁶<12¹⁶` and the ratio window give
   `11(n+d+16)<12(n+16)`.  With `d≥16`, this first gives `n≥161`.
   For each of the eight values `161≤n≤168`, exact kernel arithmetic gives

   ```
   4 B(16,n) < B(16,n+16).
   ```

   Since `B(16,x)` is increasing and `d≥16`, the equation is impossible
   on those eight values.  Thus `n≥169` and `v≥355`.

2. The same linear window gives `5w≤6v`, while `d≥16` gives
   `w≥v+32`.  Exact shifted-coefficient inequalities prove

   ```
   D(w)-4D(v) < 0,
   -16384 X < D(w)-4D(v).
   ```

   For the second inequality, substitute `v=355+a`,
   `w=387+a+b`, with `a,b≥0`.  The resulting degree-eight polynomial has
   45 nonzero coefficients; every coefficient is at least `16384`, and its
   constant coefficient is
   `6539585281315940440473600`.  There is no hidden asymptotic or
   unquantified positivity claim.

3. At every odd argument,

   ```
   16384 ∣ T(W).                                      (2)
   ```

   Indeed, write `W²=1+8u`.  Then

   ```
   T(W)=4096 G(u),
   G(u)=u⁴-42u³+483u²-1562u-732,
   ```

   and `4∣G(u)` for every integer `u`, checked algebraically in the two
   parity cases.  The Lean proof avoids division by splitting the odd
   argument modulo four.

The positivity of `T` on `[355,∞)` makes `X>0`.  Equation (1) and the two
strict deficit bounds put the integer `m` in `(-16384,0)`, while (2) makes
`m` a multiple of `16384`.  This is impossible.

## Kernel closures at `k=20` and `k=24`

The same polynomial-square identity gives wider traps at the next two rows.
All constants below are integers and every finite-field table is proved by
ordinary kernel reduction (`by decide`), never `native_decide`.

For `k=20`, exact shifted-coefficient certificates give

```
-5,853,806 < m < 0,        3,200 ∣ m.
```

Thus `m=-3200t` with `1≤t≤1829`.  The exact prime-field cover

```
p:                 227, 199, 233, 239, 211, 197, 241
survivors: 1829, 811, 355, 165,  73,  26,   9,   0
```

eliminates all candidates.  Each field lemma says that the simultaneous
congruences `S(w)=4S(v)` and `T(w)-2T(v)=-3200t` force `t mod p` into the
displayed computed mask; the final cover theorem applies those masks to the
whole integer interval.

For `k=24`, the corresponding data are

```
-5,993,518,490 < m < 0,        10,616,832 ∣ m,

p:              13, 191, 157, 227, 239, 241, 131, 197, 71
survivors: 564, 304, 170,  96,  51,  26,  11,   5,  1,  0.
```

The two main theorems and every imported finite table compile with axiom set
`[propext, Classical.choice, Quot.sound]`.

## Uniform-route audit

`even_uniform_sqrt_verify.py` constructs the polynomial part exactly for
every even `k` from 16 through 100.  If `k=2r`, its recurrence verifies

```
deg D = r-2  when r is even,
deg D = r-1  when r is odd.
```

It also computes the exact fixed divisor of `T(2t+1)` as the gcd of the
first `r+1` values.  This is the full fixed divisor: finite differences show
that an integer polynomial of degree at most `r` takes every integer value
in the integer span of any `r+1` consecutive values.

The hoped-for uniform continuation fails at the next row.  At the real
boundary `d=k`, let `v_k` be the unique positive root of

```
S(v+2k)=4S(v).
```

The verifier encloses this root by exact dyadic bisection and encloses
`H_k(v)=T(v+2k)-2T(v)` by rational interval arithmetic.  The comparisons in
the last column are exact, not decimal estimates:

| `k` | integral scale `c` | odd fixed divisor of `T` | first admissible odd center | `|H_k(v_k)|` vs. fixed divisor |
|---:|---:|---:|---:|:---|
| 16 | 1 | 16384 | 355 | below |
| 18 | 128 | 81 | 451 | above |
| 20 | 1 | 3200 | 559 | above |
| 24 | 1 | 10616832 | 809 | above |
| 32 | 1 | 3221225472 | 1447 | above |
| 50 | 4194304 | 15625 | 3559 | above |
| 100 | 1 | 589824000000000000 | 14329 | above |

Thus the simple `k=16` mechanism, "trap `m` between zero and the first
nonzero fixed-divisor multiple," does not extend even to `k=18`.  This is a
route obstruction, not a counterexample to Target 2: the real boundary
point is not asserted to have integral centers, and a stronger modular or
row argument could still eliminate the many possible multiples of the
fixed divisor.

## Exact `k=18` trap and modular audit

For `k=18`, the exact polynomials are

```
T(W) = 128W⁹ - 62016W⁷ + 9038832W⁵
       - 439659848W³ + 3788405307W,

D(W) = 78397083729792W⁸ - 16673477276146464W⁶
       + 945705074655002832W⁴ - 9110023357135451751W²
       + 19455213098280960000.
```

The odd fixed divisor is exactly `81`.  Monotonicity of
`S(v+36)/S(v)` and exact evaluation at adjacent odd integers force
`v≥451`.  The ratio bracket `4·12¹⁸<13¹⁸` gives `11w≤12v`;
also `w≥v+36`.

Put `B=731939653`.  After substituting `v=451+a` and
`w=487+a+b`, every one of the 55 coefficients of

```
D(w) + B T(w) + 2B T(v) - 4D(v)
```

is positive for `a,b≥0`; the least is `93688275584`.  A separate
nine-coefficient shifted certificate, using `11w≤12v`, makes
`D(w)-4D(v)<0`.  Therefore every hypothetical integer solution obeys the
rigorous trap

```
-731939653 < m < 0,        81 ∣ m.
```

Since

```
731939652 = 81 · 9036292,
```

this leaves exactly 9,036,292 values `m=-81t`.

`k18_modular_scan.py` evaluates the two equations

```
S(w)=4S(v),       T(w)-2T(v)=-81t
```

over prime fields.  Applying every prime `p≤1000` to the full trapped
list leaves exactly

```
t = 2990977, 3541067,
m = -242269137, -286826427.
```

Both remaining values have an explicit local pair `(w,v)` for every prime
`p≤5000`; the SHA-256 digest of the canonical witness list is

```
0fa2129abda0244e9e07c1010600c4dd23f812798f74e5b62b834cbeb7a89f9b
```

Thus no product of distinct tested primes can eliminate these two values:
their individual local points combine by CRT.  This does not audit prime
powers beyond the first power and does not prove local solubility for every
prime; it is a precise obstruction to the natural finite prime-field cover
through 5000.

## Exact second-stage closure of `k=18`

The two global survivors can nevertheless be removed without a local
obstruction.  If `d≥56`, the exact power bracket

```
4·12¹⁸ < 13¹⁸
```

forces `n≥655`, hence `v≥1329` and `w≥v+112`.  On writing
`v=1329+a`, `w=1441+a+b`, every one of the 55 coefficients of

```
D(w) + 242269137 T(w) + 2·242269137 T(v) - 4D(v)
```

is positive; the least is `31010449536`.  Therefore

```
m > -242269137.
```

This strict inequality excludes both modular survivors, one of which is
exactly the excluded endpoint and the other of which lies below it.

Equivalently, the large-gap case can be audited as a standalone finite cover.
Since `81∣m`, it leaves `m=-81t` with `1≤t≤2990976`.  The following 35
prime fields eliminate that entire interval, with exact survivor counts
recorded by `k18_archimedean_closure_verify.py`:

```
19, 907, 827, 941, 887, 857, 991, 919, 967, 911, 883, 947,
839, 997, 821, 751, 769, 547, 859, 659, 977, 797, 491, 811,
757, 809, 509, 619, 281, 677, 773, 431, 593, 487, 163.
```

For the remaining strip `18≤d≤55`, exact ratio brackets force the finite
window

```
12d-17 ≤ n ≤ floor((25d-3)/2).
```

There are exactly 1,311 pairs in this window.  Direct integer evaluation of
`S(2(n+d)+19)-4S(2n+19)` is nonzero at every pair.  The smallest absolute
value is

```
2307600880601197152466465133764408497930240000
```

at `(d,n)=(19,228)`.  This completes the exact-arithmetic proof for `k=18`.

The finite certificate is now kernel-banked.  To keep each declaration
bounded, the Lean proof uses a reordered 62-prime subcover with maximum prime
`857`.  The `p=19` condition leaves exactly the four classes
`t mod 19 ∈ {1,3,16,18}`.  Writing `t=19q+r` gives `q<157420`.

For each remaining prime, the field theorem is split into outer-center ranges
of at most 128 values: 190 ordinary-`decide` shards in total.  The quotient
range is certified by 77 balanced scans, each covering `2¹¹` consecutive
values, followed by seven group glues and one top-level cover.  This avoids
both the linear recursion depth of `∀ t : Fin 2990977` and the memory peak of
a single million-pair field table.  Every shard uses ordinary kernel
reduction; there is no `native_decide`.

The 62-prime order and its per-prime survivor counts are reproduced exactly
as `KERNEL_COVER` and `KERNEL_COVER_COUNTS`.  The last counts are
`..., 5,4,3,2,1,0`.

## Reproduction

```bash
lake build ErdosProblems.Erdos686EvenK16
lake build ErdosProblems.Erdos686EvenK18
lake build ErdosProblems.Erdos686EvenK182024
python3 compute/campaign686/agent_t2_even_uniform_sqrt/even_uniform_sqrt_verify.py
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k18_modular_scan.py
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k18_archimedean_closure_verify.py
python3 compute/campaign686/agent_t2_even_uniform_sqrt/k20_k24_cover_verify.py
python3 -m pytest -q compute/campaign686/agent_t2_even_uniform_sqrt
```

All four Lean theorems report exactly the permitted kernel axioms
`[propext, Classical.choice, Quot.sound]`; there is no `native_decide`.
