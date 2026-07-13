# Hostile audit: supplied-owner matched residual dichotomy

Verdict: **PASS as a kernel-banked supplied-owner dichotomy; FAIL as a full
Erdős 686 closure**.

## Dependency tree

```text
exact quotient-four equation and supplied q-owner data
├── sharp centered ratio                                  [Lean PASS]
│   └── 1218443*k*b < 3707904*a; hence 0<b<a       [Lean PASS]
├── arbitrary-modulus matched square lift                    [Lean PASS]
│   └── q | D                                             [Lean PASS]
└── split on D
    ├── D != 0
    │   ├── q <= |D|                                      [Lean PASS]
    │   ├── |D| < 2a(C_j+2C_i)                            [Lean PASS]
    │   └── explicit gap bound                           [Lean PASS]
    └── D = 0
        ├── gcd normalization a=Bw, a+b=Aw                  [Lean PASS]
        ├── 0<B<A<2B                                      [Lean PASS]
        ├── Z | c2 from exact second-order expansion         [Lean PASS]
        ├── c2 != 0 from strict harmonic slopes              [Lean PASS]
        └── Z and d fixed-coefficient bounds                 [Lean PASS]
```

## Per-node verdicts

| Node | Verdict | Exact audit |
|---|---|---|
| modulus assumptions | PASS | The core assumes only `q>0`; it does not hide primality, oddness, or owner uniqueness. |
| sharp cofactor comparison | PASS | Constants are exactly `1218443` and `3707904`; no asymptotic term is suppressed. |
| residual divisibility | PASS | The existing square lift gives `q^2 | qD`, and Lean cancels `q` using its explicit positivity. |
| nonzero absolute bound | PASS | The quantified strict bound is `|D|<2a(C_j+2C_i)` and uses `b<a` plus `C_j>0`. |
| zero normalization | PASS | `A=4C_i/g`, `B=C_j/g`, `g=gcd(4C_i,C_j)` are returned in the final theorem, together with exact `w,Z` witnesses. |
| quadratic divisibility | PASS | The proof expands both local cofactors modulo `Z^2`, cancels the already-zero constant and linear terms, then cancels one positive `Z`. |
| quadratic nonvanishing | PASS | It casts to exact rationals, uses the strictly decreasing owner slope, and derives `C_j<=C_i`; the normalized magnitude equality would force `4B<=A`, contradicting `A<2B`. |
| kernel gate | PASS | Final and key intermediate theorems print only `[propext, Classical.choice, Quot.sound]`; no `native_decide` or placeholder is used. |
| full closure | FAIL | No theorem supplies a contradiction-producing matched owner for every remaining equation. |

Every qualitative phrase has a quantified replacement above.  In particular,
"fixed" means the displayed integer
`(A-B)*|A^2 E_j-4B^2 E_i|+k-1`, depending only on `k,i,j` through the gcd
normalization.

## Boundary and falsification audit

- **Odd center:** for `k=17,i=j=9`, the harmonic slope and `c2` vanish at
  `(A,B)=(4,1)`.  This is not a counterexample because `4<2` is false.  The
  hypothesis `A<2B` is explicit in Lean.
- **`q=k`:** a synthetic exact transfer at `q=k=17` has one lower and one
  upper landing.  The proof itself uses no strict `q>k`; a length-`k` block
  has diameter `k-1`.
- **`p=2`:** irrelevant to the prime-owner corollary when `p>=k>=16`, while
  the arbitrary-`q` core remains valid for every positive modulus.
- **`d=1`:** `(k,n,d)=(6,1,1),(9,2,1),(15,4,1)` are genuine quotient-four
  telescopes, including both mandatory odd rows.  They are excluded exactly
  by `d>=k`, which is also what forces `b>0`.
- **row 22:** the named point is not an equation.  Both narrow normalized
  pairs give `(A,B)=(16,15)`,
  `c2=104810845224960000`, and gap ceiling
  `104810845224960021>d`.
- **row 984:** the named point is not an equation.  Its factor `7237` has no
  upper owner landing, so it cannot be smuggled into the supplied-match
  hypothesis.

The exact Python verifier uses only integers and `Fraction`.  Its scan through
`k=300` is not cited as the proof of uniformity; it adversarially reproduces
the symbolic Lean theorem and named boundaries.

## Circularity audit

The final theorem assumes the exact block equation because it derives a
necessary dichotomy for hypothetical solutions.  Neither disjunct assumes
the desired contradiction.  The zero branch does not assume `c2!=0`; that is
proved from strict slope order.  The theorem also does not rename the target
as an owner-supply premise: exact lower and upper factorizations are plainly
listed as hypotheses.

## Exact remaining gap

The missing node is an owner-supply or global aggregation theorem strong
enough to make one of the two explicit bounds contradictory for every
remaining solution.  A theorem merely asserting that some large owner exists
is insufficient unless it also controls the cofactor in the nonzero arm or
forces the fixed zero arm.  Multiplying edgewise inequalities without
controlling repeated lower vertices is invalid; degree-two cycles are the
recorded surviving obstruction.
