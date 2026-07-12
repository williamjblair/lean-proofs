# Large-prime gap components and prime-power Lucas structure

Date: 2026-07-12

This lane began from the exact binomial rewrite

\[
 B(k,x)=k!\binom{x+k}{k},\qquad
 \binom{n+d+k}{k}=4\binom{n+k}{k}.
\]

It found two genuinely new restrictions.  The first is the stronger one and
is fully elementary.

## 1. Large-prime component theorem

Let

\[
 k\ge16,\quad d\ge k,\quad p\text{ prime},\quad p\ge k,
 \quad e>0,\quad p^e\mid d.
\]

Then a quotient-four solution necessarily satisfies

\[
 \boxed{6p^{2e}< (13k-6)d+18(k-1).}
\]

Equivalently, the reverse weak inequality is an explicit no-solution
certificate.  Notice all boundary choices: `p=k` is allowed, `e=1` is
allowed, and `p^e` need only divide `d`.

### Proof

The exact upper endpoint window is

\[
 4(n+1)^k\le(n+d+1)^k.
\]

For every `k>=1`,

\[
 (13k+18)^k<4(13k)^k.
\]

Indeed, `1+x<exp(x)` with `x=18/(13k)` gives the left ratio below
`exp(18/13)`.  Mathlib's rigorous four-term exponential remainder bound at
`9/13` gives

\[
 \exp(9/13)\le \frac{1827191}{913952}<2,
\]

so `exp(18/13)<4`.  Exact power linearization now yields

\[
 18(n+1)<13kd. \tag{1}
\]

The existing local quadratic lift localizes `p^e` at a unique
`i in {1,...,k}` and proves

\[
 p^{2e}\mid 3(n+i)-d. \tag{2}
\]

The banked lower ratio window gives `9d<n`; hence the residual in (2) is
positive, and

\[
 6p^{2e}+6d\le18(n+i)
 \le18(n+1)+18(k-1)
 <13kd+18(k-1). \tag{3}
\]

Since

\[
 13kd+18(k-1)=((13k-6)d+18(k-1))+6d,
\]

(3) is exactly the boxed strict inequality.

The isolated Lean module is
`ErdosProblems/Erdos686LargePrimeGapComponent.lean`.  Its public theorem
surface is:

- `thirteen_k_add_eighteen_pow_lt_four_mul_thirteen_k_pow`;
- `eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution`;
- `no_four_solution_of_large_prime_gap_component_dominance`;
- `large_prime_gap_component_square_strict_upper_of_four_solution`;
- `no_four_solution_gap_eq_large_prime_power_of_three_k_le`;
- `no_four_solution_gap_eq_large_prime_power_exponent_ge_two`.

The direct Lean check passes for every theorem in this list, with the exact
axiom report `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

### Infinite closed subclass

More generally, if `d=p^e`, `p>=k`, `e>0`, and `3k<=d`, then

\[
 18(k-1)\le6d,
 \qquad
 (13k-6)d+6d=13kd\le6d^2=6p^{2e}.
\]

Thus every such whole prime-power gap is excluded for every `k>=16`, including
every prime gap `d=p>=3k`.  Exponent `e>=2` is an automatic specialization,
because `p^e>=p^2>=3k`.  This is an unbounded infinite family of rows, prime
bases, and gaps.  The small exponent-one boundary is real: at
`(k,p,e,d)=(16,17,1,17)` the dominance inequality fails, while
`(16,101,1,202)` shows that an `e=1` component can close even when `p^e` is
only a proper divisor of the gap.

## 2. Lucas/Kummer prime-power boundary

Put `q=p^a` and `k=q-1`.  Exact Lucas arithmetic gives

\[
 \binom{x+q-1}{q-1}\equiv
 \begin{cases}1& q\mid x,\\0&q\nmid x\end{cases}\pmod p. \tag{4}
\]

For `p>=5`, (4) implies that a quotient-four solution cannot have `q|n`:
the equation first forces `q|(n+d)`, then reads `1=4 (mod p)`.  The same
argument applied symmetrically excludes `q|(n+d)`.  This is a proper boundary
restriction, not a closure of the nonzero-residue branch.

The isolated Lean source
`ErdosProblems/Erdos686PrimePowerBinomialBoundary.lean` now contains the
full endpoint surface:

- `choose_prime_pow_pred_modEq_one_of_dvd`;
- `choose_prime_pow_pred_modEq_zero_of_not_dvd`;
- `prime_power_pred_choose_ratio_four_endpoints_not_dvd`;
- `prime_power_pred_four_solution_endpoints_not_dvd`.

The direct kernel check now passes for all four declarations, reporting
exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.  The public
endpoint theorems are slightly stronger than the FinalResidual conjunct: they
also handle the degenerate `a=0` equation by contradiction, while the residual
keeps `0<a` to describe genuine rows.

The exact non-mutating integration recipe for both restrictions is recorded
in `final_residual_snippet.md`.

The exact verifier also reproduces the sharper Kummer/unit formula.  If
`x=qs+r`, `0<r<q`, then

\[
 v_p\binom{x+q-1}{q-1}=a-v_p(r)+v_p(s+1),
\]

and its `p`-free unit is
`unit_p(s+1)/unit_p(r) (mod p)`.  This formula has not been promoted into the
shared theorem surface; it remains secondary to the endpoint theorem and the
fully checked component theorem.

Combining both endpoint formulas does give one genuinely stronger
equation-facing filter.  With `n=qs+r`, `n+d=qS+R`, set
`A=(S+1)r`, `B=(s+1)R`.  Any exact equation forces
`v_p(A)=v_p(B)=V` and

\[
A/p^V\equiv4(B/p^V)\pmod p.
\]

The full derivation, the endpoint-only falsifier `(p,a,n,d)=(5,1,1,5)`, and
the surviving tuple `(5,1,1,7)` are recorded in
`kummer_unit_restriction.md`.  An exact `p=5,a=1` census leaves 774 of 4,728
admissible tuples, so this is a proper filter rather than a congruence
closure.  It is not claimed as kernel-banked.

## Exact reproduction

Run:

```text
python3 compute/campaign686/agent_t2_binomial_kummer/verify.py
python3 -m pytest -q compute/campaign686/agent_t2_binomial_kummer/test_verify.py
```

The verifier uses Python integers only.  It checks the block/binomial bridge,
Lucas delta, Kummer valuation and unit formulas, the derived unit filter, the
power bracket through
`k=5000`, complete Lucas endpoint residue grids, exhaustive small
upper-window tuples, the component arithmetic,
`p=k`, `p>k`, `e=1`, `e=2`, proper component divisibility, and the mandatory
fixtures.

## Exact remaining scope

This theorem does not assert that every mixed gap has a prime component
satisfying the dominance inequality.  A hypothetical solution is now forced
into the quantified complementary region

\[
 \forall p,e,\quad
 [p\text{ prime}\land p\ge k\land e>0\land p^e\mid d]
 \Longrightarrow
 6p^{2e}<(13k-6)d+18(k-1).
\]

Small-prime-supported and non-dominant mixed gaps remain live.
