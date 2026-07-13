# Adversarial audit: k=22 Archimedean core

## Claimed result

For every hypothetical row-22 solution with gap `d >= 250`, there are
integers `w,v` and a natural number `t` such that

```text
S(w) = 4 S(v),
T(w) - 2 T(v) = -33 t,
1 <= t <= 3795146531,
Odd t.
```

For `22 <= d <= 249`, no solution exists.  This file does not claim the
finite local-cover contradiction for the displayed large-gap surface.

## Dependency tree and verdicts

1. Imported ratio window and quadratic-strip theorem.
   - Dependency: the banked `ratio_window_four_nat`,
     `ratio_window_linearize_of_pow_bracket`, and
     `no_four_solution_of_quadratic_strip` theorems.
   - Use: the quadratic theorem covers exactly `22 <= d <= 26`; the ratio
     window gives `15d < n+22` and `5(n+1) < 77d`.
   - Verdict: kernel dependency, not a new assumption.
2. Centered polynomial identities.
   - Claims: `T(W)^2 = 65536 S(W)+D(W)` and
     `S(2x+23)=4194304 blockProduct(22,x)`.
   - Verdict: proved by ring normalization and the banked centered-product
     identity.
3. Divisor and parity.
   - Claims: `33 | T(2a+1)` for every integer `a`; every integer dividing
     all such values divides 33; and every `T(2a+1)` is odd.
   - Witness for maximality:
     `-72113493154*T(1) + 39309729457*T(3) = 33`.
   - Verdict: divisibility checked over `ZMod 33` by ordinary `decide`;
     maximality and parity are symbolic kernel proofs.
4. Finite strip.
   - Quantified domain: every `27 <= d <= 249` and every natural `n`
     satisfying `15d < n+22` and `5(n+1) < 77d`.
   - Exact normalization: `n=15d-21+a` with `0 <= a < 120`; also
     `n < 3834`.
   - Exact count: 16,859 admissible `(d,n)` pairs.
   - Verdict: 28 chained ordinary-`decide` shards plus a symbolic router;
     all modules build.
5. Large-gap Runge trap.
   - Quantified domain: every hypothetical solution with `d >= 250`.
   - Forced bounds: `n >= 3729`, `v >= 7481`, `w >= v+500`, and
     `14w <= 15v`.
   - Error bound: for `m=T(w)-2T(v)`,
     `-125239835548 < m < 0`.
   - Dividing by 33 gives exactly
     `1 <= t <= floor(125239835547/33)=3795146531`.
   - Verdict: the lower and upper polynomial inequalities are proved from
     coefficientwise shifted inequalities in Lean; quotient extraction and
     parity are symbolic.
6. Conditional row closure.
   - Dependency: a contradiction for every odd candidate on the exact
     surface in the claimed result.
   - Verdict: exposed as
     `no_gap_solution_four_even_twentytwo_of_large_obstruction`; no finite
     cover is smuggled into this module.

## Boundary and falsification checks

- Quadratic boundary: `18*26 <= 22^2 < 18*27`; no gap 27 is routed to the
  quadratic theorem.
- Finite/large boundary: the finite shards end at `d=249`; the Runge theorem
  begins at `d=250`.
- Strict Runge boundary: `m > -125239835548`, so the natural candidate cap
  uses `125239835547`, not `125239835548`.
- The unrestricted-root fixtures from the earlier falsification record are
  reproduced exactly:
  `(t,w,v)=(28643526033,-3,-1)`, `(19687413989,-7,-1)`, and
  `(3809308513,13,15)`.  Each satisfies the two polynomial equations, and
  each has `t > 3795146531`; none contradicts this reduction.
- `native_decide`, `sorry`, and `admit` do not occur in any generated module.

## Exact remaining lemma

The only missing statement needed by the conditional closure is

```text
forall (w v : Int) (t : Nat),
  S(w) = 4*S(v) ->
  -(33*(t:Int)) = T(w)-2*T(v) ->
  1 <= t -> t <= 3795146531 -> Odd t -> False.
```

This is the packed finite local-cover obligation.  It is not claimed here.
