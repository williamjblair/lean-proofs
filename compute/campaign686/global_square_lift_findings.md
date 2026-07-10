# Erdős 686 global quadratic residual lift

Status: **Lean-banked; independent hostile audit passed.**

For

```text
X_i = 3(n+i)-d,
Q(z) = product_{i=1}^k (X_i+z),
```

the exact block equation becomes

```text
Q(4d)=4Q(d).                                             (1)
```

Write `Q(z)=sum_r c_r z^r`.  Adding `3Q(0)` to the two sides of
(1) gives

```text
Q(4d)-4Q(d)+3Q(0)
  = sum_{r>=2} (4^r-4)c_r d^r.                          (2)
```

The constant coefficient cancels, the linear coefficient vanishes because
`4^1-4=0`, and `3` divides `4^r-4` for every `r`.  Equation (1) therefore
turns (2) into the exact identity

```text
Q(0) = d^2 * sum_{r>=2} ((4^r-4)/3)c_r d^(r-2).         (3)
```

Consequently

```text
d^2 | product_{i=1}^k (3(n+i)-d).                       (4)
```

This has no primality, prime-support, localization, parity, or small-prime
exception.  It is a proper consequence of the exact equation, not a
replacement hypothesis equivalent to either open target.

The Lean module proves both the signed statement and a natural-number wrapper
in the live `k>=5`, `d>=k` range, where the already-banked ratio inequality
makes every residual positive.

## Why it is useful

The earlier local square lifts assign prime-power components one at a time
and pay a derivative/concentration loss at small bases.  Equation (4) first
places the entire square `d^2` into a single length-`k` arithmetic
progression of residuals.  A later valuation-concentration step can therefore
pay only the progression loss, which is potentially much smaller.  No claim
that this alone closes a mixed-prime tail is made here.

## Boundary audit

- The signed theorem is over `Int`, so a negative residual causes no hidden
  natural subtraction and its proof uses no positivity assumption.  The
  separate natural-number wrapper uses the banked ratio bound to justify its
  casts from natural subtraction.
- At `d=0`, the polynomial lemma remains valid: its ratio premise forces the
  constant value to vanish.  For the block equation itself, `d=0` would say
  `B(k,n)=4B(k,n)`, impossible because the block product is positive.
- At `k=0`, both block products are `1`, so the equation premise is again
  impossible.  At `k=1`, the equation is equivalent to
  `d=3(n+1)`, and the unique residual is exactly zero; the square divisibility
  is therefore valid at this boundary as well.
- The exact small scan reproduces the `d=1` telescopes at lengths
  `3,6,9,12,15` and checks (3) on each of them.
- The two named large-`k` prefix fixtures are not equation solutions, so the
  theorem correctly makes no assertion about them.

## Reproduction

```bash
python3 -m pytest compute/campaign686/test_global_square_lift_verify.py -q
python3 compute/campaign686/global_square_lift_verify.py
lake env lean ErdosProblems/Erdos686GlobalSquareLift.lean
```
