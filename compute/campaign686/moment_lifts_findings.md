# Erdős #686: global cubic moment lifts

Status: **Lean candidate; independent hostile audit passed.**

The already-banked global residual square lift uses `4^1=4` to cancel the
linear coefficient.  The second identity `2^2=4` cancels the quadratic
coefficient and gives two new unconditional cubic divisibility combinations.

For an integer polynomial `P(z)=sum c_j z^j`, direct monomial expansion gives

```text
d^3 | P(2d)-4P(d)+3P(0)+2d c_1,                  (1)
d^3 | P(2d)-4P(-d)+3P(0)-6d c_1.                (2)
```

The terms of degrees zero and one are canceled by the displayed corrections,
the degree-two term vanishes because `2^2=4`, and every remaining monomial
contains `d^3`.

Apply (1) to

```text
P_-(z)=product_i (z+n+i-d).
```

Then `P_-(d)=B(k,n)` and `P_-(2d)=B(k,n+d)`, so every exact multiplier-four
equation forces

```text
d^3 | 3P_-(0)+2d [z]P_-.                         (3)
```

Apply (2) to

```text
P_+(z)=product_i (z+3(n+i)+d).
```

Its evaluations at `-d` and `2d` are respectively `3^k B(k,n)` and
`3^k B(k,n+d)`, giving

```text
d^3 | 3P_+(0)-6d [z]P_+.                         (4)
```

These are cubic **combinations**, not claims that either constant product is
itself divisible by `d^3`.  They are proper consequences of the equation and
introduce no prime-support, smoothness, or target-strength hypothesis.  Their
intended next use is as independent valuation information for the residual
bucket regime with at least three prime components.

## Hostile-audit verdict

- Direct expansion of a monomial `a z^m` gives
  `a(2^m-4)d^m` in (1) for `m>=3` and
  `a(2^m-4(-1)^m)d^m` in (2).  The tests reproduce both formulas for
  degrees `0..12`, positive and negative coefficients, and `-6<=d<=6`.
- The lower residual evaluations are exactly `B(k,n)` and `B(k,n+d)`.
  The reflected upper evaluations are exactly `3^k B(k,n)` and
  `3^k B(k,n+d)`.  An exact grid checks all four equalities, including
  `k=0` and `d=0`.
- At `d=0`, both corrected polynomial differences are exactly zero.  The
  block premise itself is impossible because `B(k,n)>0`.  At `k=0`, both
  block products are `1`, so the premise is again impossible.
- The small scan checks every equation solution with `1<=k<=15` and
  `0<=n<40`, `1<=d<40`, including all five `d=1` telescopes in that box.
  The two named large-`k` row-prefix fixtures fail the equation premise and
  therefore trigger no divisibility claim.
- The module builds with Lean `4.29.1`; all twelve public lemma/theorem
  constants report exactly `[propext, Classical.choice, Quot.sound]`.  The
  Lean and Python sources pass the forbidden-declaration scan.

The audit therefore accepts (3) and (4) as genuine proper consequences of
the exact block equation.  It specifically rejects the stronger inference
`d^3 | P_-(0)` or `d^3 | P_+(0)`: neither theorem states it, and the displayed
linear-coefficient correction cannot be discarded without an additional
argument.  Indeed, the exact solution `(k,n,d)=(1,0,3)` has
`P_-(0)=-2`, `P_+(0)=6`, and `d^3=27`; both stronger product-divisibility
claims fail while both corrected combinations vanish.

## Reproduction

```bash
python3 -m pytest compute/campaign686/test_moment_lifts_verify.py -q
python3 compute/campaign686/moment_lifts_verify.py
lake env lean ErdosProblems/Erdos686MomentLifts.lean
lake build ErdosProblems.Erdos686MomentLifts
```
