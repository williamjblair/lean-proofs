# Hostile audit: large-prime component and Lucas restrictions

Date: 2026-07-12

## Claim boundary

The bankable claim is a necessary inequality for every prime-power component
of the gap whose prime base is at least the row length.  Its whole
prime-power `e>=2` corollary is a genuine infinite closed subclass.  It is not
Target 2 and makes no claim about gaps supported on primes below `k`.

The Lucas result is a second, proper residue restriction for rows
`k=p^a-1`; it is explicitly not treated as a pure-congruence closure.

## Dependency tree

| Node | Exact statement | Dependency | Verdict |
|---|---|---|---|
| P1 | `(13k+18)^k < 4(13k)^k`, `k>=1` | `1+x<exp x`; Mathlib certified remainder for `exp(9/13)` | proved in isolated Lean |
| P2 | `18(n+1)<13kd` | P1 and the exact upper endpoint power window | proved in isolated Lean |
| P3 | `p^e` has one lower owner for prime `p>=k` | banked consecutive-block localization | already kernel-banked |
| P4 | `p^(2e) | 3(n+i)-d` | banked local quadratic lift | already kernel-banked |
| P5 | `0<3(n+i)-d` | banked `9d<n`, `i>=1` | exact arithmetic |
| P6 | `6p^(2e)<(13k-6)d+18(k-1)` | P2--P5 and `i<=k` | proved in isolated Lean |
| P7 | no solution if the reverse weak inequality holds | P6 | proved in isolated Lean |
| P8 | no solution for `d=p^e`, `p>=k`, `e>0`, `3k<=d` | P7 and exact dominance arithmetic | proved in isolated Lean |
| P9 | no solution for `d=p^e`, `p>=k`, `e>=2` | P8 and `p^e>=p^2>=3k` | proved in isolated Lean |
| L1 | `B(k,x)=k!*C(x+k,k)` | factorial identity | proved in isolated Lean |
| L2 | Lucas delta (4) | Mathlib Lucas theorem and induction on `a` | proved in isolated Lean |
| L3 | `p>=5`, `q=p^a=k+1` implies `q nmid n,n+d` | L2 and quotient four | proper restriction; proved in isolated Lean |
| L4 | equal combined valuations and normalized unit congruence | exact Kummer/unit formula | strictly stronger paper-level filter; 774/4728 survive; not Lean-banked |

No `native_decide`, floating point, private theorem-strength assumption, or
external number-theory theorem is used by P1--P9.

The direct checks of both isolated Lean modules report exactly
`[propext, Classical.choice, Quot.sound]` for P1, P2, P6--P9 and L1--L3, with
no `sorryAx`.

L4 is not included in the FinalResidual snippet.  Its exact endpoint-only
falsifier is `(p,a,n,d)=(5,1,1,5)`; its exact live witness is `(5,1,1,7)`.
Thus it passes the requested `p=5,a=1` hostile check but cannot be upgraded to
a closure.

## Boundary audit

### Strict residual boundary

P4 permits equality `p^(2e)=3(n+i)-d`.  The proof still contradicts the weak
dominance hypothesis because P2 is strict.  The theorem correctly accepts
`<=`, not merely `<`, in its no-solution premise.  The zero residual is
impossible by `9d<n`.

### `p=k` versus `p>k`

The local uniqueness and derivative cancellation are valid at `p=k`, because
two owner indices differ by at most `k-1`.  The theorem therefore uses
`k<=p`.  The verifier checks prime rows with `p=k` separately from the first
prime `p>k`.

### `e=1` versus `e=2`

The component theorem itself allows every positive exponent.  The size-form
whole-gap corollary includes `e=1` when `d=p>=3k`; the automatic corollary
without an extra size premise starts at `e=2`.  Exact witness

```text
(k,p,e,d)=(16,17,1,17)
```

fails the dominance premise, so silently dropping `3k<=d` at `e=1` would be
false.  Every tested `e=2` boundary satisfies it, and P9 proves this uniformly.

### Component divides the gap versus equals the gap

P6 needs only `p^e|d`.  The exact proper-component example

```text
(k,p,e,d)=(16,101,1,202)
```

satisfies the dominance premise even though `p^e<d`.  P8 and P9 use equality
only to prove dominance automatically.

### `k=16`

All analytic and arithmetic constants are checked at the minimum row.  P1 in
fact holds from `k=1`; `k>=16` is used for the banked `9d<n` theorem and the
large-row target.

### `d=k` and published external branches

The new proof does not use the external Erdős--Selfridge concatenated-square
argument at `d=k`, nor any Erdős--Straus or Saradha--Shorey theorem.  At
`d=k`, a component with `p>=k` can only be the `p=k,e=1` boundary, and its
dominance premise fails in the checked range.  Therefore no external `d=k`
or nearby `k+1` claim is silently counted as kernel-banked progress.

### Lucas base boundaries

The endpoint contradiction is `1=4 (mod p)`, so `p>=5` is material.
For `p=3`, the two residues agree; for `p=2`, multiplication by four changes
the 2-adic valuation.  Neither base is claimed.  The exponent hypothesis
`a>0` keeps the statement on genuine rows `k=p^a-1`; `a=0` would be the
degenerate zero-length row.

## Mandatory falsification fixtures

| Fixture | Exact outcome |
|---|---|
| `k=9,15`, `d=1` telescopes | Outside `k>=16,d>=k`; no conclusion applied. |
| `(984,3177026,4480)` | `4480` has no prime divisor `p>=984`; P6 is inapplicable. |
| `(244,48502,277)` | The only eligible component is `(p,e)=(277,1)`, and its dominance inequality is false.  The row-prefix survivor is not excluded. |
| MalekZ all-moduli family | P6 uses a global size window plus a lifted square divisibility, not a finite congruence obstruction. |

For the Lucas lane specifically, `k=9` has `k+1=10`, not a prime power, and
`k=15` has `k+1=16` with base `p=2`, outside `p>=5`.  Thus the `d=1`
telescopes are not falsely excluded.  L3 is only a conditional boundary
restriction, so MalekZ-style all-moduli solvability remains compatible with
it.

The two large fixtures are row-skeleton survivors, not exact product
solutions.  No equation consequence is inferred from their prefix behavior.

## Computational reproduction verdict

`verify.py` and `test_verify.py` use exact integer arithmetic.  They reproduce
P1 through `k=5000`, exhaust Lucas endpoint residue grids, small instances of
P2, and the post-lift chain,
prove the advertised boundary examples numerically, and audit the Lucas and
Kummer formulas.  Their computations are regression checks; P1--P9 rest on
the Lean proof, not on finite search.

## Remaining quantified region

Every still-hypothetical solution must satisfy

\[
\forall p,e,
\quad p\text{ prime}\land p\ge k\land e>0\land p^e\mid d
\Longrightarrow
6p^{2e}<(13k-6)d+18(k-1).
\]

No claim is made that negating this region is easier than Target 2; the
progress is the new explicit component restriction and the infinite
whole-prime-power subclass.
