# Target 2 reflected-alignment square lift

Status: **two new proper equation-level restrictions, Lean-banked in isolated
modules; `LargeKSmoothHypothesis` remains open.**

## Exact statement

Let

```text
k >= 16,  k <= d,
B(k,n+d) = 4 B(k,n),
S = 2n+d+k+1.
```

For every prime `p>k` with `p|S`, put `e=v_p(S)` and `q=p^e`.  Then there is
an index `i in {1,...,k}` such that, with

```text
A = n+i,
B = n+d+(k+1-i),
```

one has

```text
q | A,  q | B,
q^2 | (-1)^(k-1) B - 4A.                         (1)
```

Consequently

```text
q^2 <= 7n.                                        (2)
```

Thus a hypothetical Target 2 solution cannot have a reflection-center prime
power with base above `k` and square larger than `7n`.  In particular, this
closes the subcase where such a dominant prime power occurs.  It does not
show that every reflection center has one.

The Lean surfaces are:

```text
matched_owner_local_coefficients_dvd_sq
localBlockCoefficient_reflected_agent
reflected_owner_local_coefficient_dvd_sq
reflected_owner_local_coefficientNat_dvd_sq
primePower_reflected_owner_dvd_sq
reflectionResidualExponent_eq_center_factorization_of_large_prime
exists_large_prime_reflection_center_square_lift_four
exists_large_prime_reflection_center_power_sq_le
```

Every surface reports exactly
`[propext, Classical.choice, Quot.sound]`.

## One/two reflected-owner center exclusion

The square lifts also interact globally.  Under the same equation and target
range, suppose the complete reflection center is exactly

```text
S = q r,
q = p^v_p(S),  r = ell^v_ell(S),
p,ell prime,  p>k, ell>k.
```

Then no solution exists.  The Lean theorem is

```text
no_four_solution_of_reflection_center_two_large_prime_powers
```

and its two arithmetic cores are

```text
no_even_two_factor_reflected_square_lifts
no_odd_two_factor_reflected_square_lifts.
```

All three report exactly `[propext, Classical.choice, Quot.sound]`.

The prime-count statement is strictly strengthened by

```text
no_four_solution_of_one_large_supported_reflected_owner_factor
no_four_solution_of_two_large_supported_reflected_owner_factors.
```

Here `q` and `r` may each aggregate arbitrarily many complete prime-power
components: every prime divisor of each aggregate need only exceed `k`.
If all components in an aggregate occupy the same reflected owner, their
coprime product divides both owner terms.  The generic weighted square lift
then gives `q^2 | C_i L_i` (or `q^2 | C_i M_i`); large prime support makes
`q` coprime to the factorial weight `C_i`, so the full aggregate square can
be cancelled.  Thus, if the center has no prime divisor at most `k`, all its
large components must occupy at least three distinct reflected owners.

For even `k`, put

```text
L_i = B_i + 4 A_i = 5n+d+k+1+3i.
```

The two square lifts give `L_i=q^2 u` and `L_j=r^2 v`, with positive
integers `u,v`.  Direct use of `d>=k`, `9d<n`, and `1<=i,j<=k` gives the
strict rational window

```text
5 S^2 < L_i L_j < 8 S^2.
```

Since `S=qr`, one has `uv in {6,7}`.  The case `uv=6` is impossible modulo
3: both `q` and `r` are powers of primes above `k>=16`, so their nonzero
squares are 1 modulo 3, while none of `(1,6),(2,3),(3,2),(6,1)` has equal
coordinates modulo 3.  If `uv=7`, the only pairs are `(1,7)` and `(7,1)`.
In the first orientation, equality of the two closed forms forces
`5r<2q`, while the coefficient-one equation `L_i=q^2` and positivity of
`d+k+1-2i` force `2q<5r`.  The other orientation is symmetric.

For odd `k`, put

```text
M_i = 4 A_i - B_i = 3n-d-k-1+5i.
```

Here the exact window is

```text
S^2 < M_i M_j < 4 S^2,
```

so `uv in {2,3}`.  Neither 2 nor 3 is a ratio of two nonzero quadratic
residues modulo 5, contradicting the two square-lift equations.  Every
strict comparison above is proved over natural numbers in Lean; no decimal
or asymptotic estimate occurs.

The one-owner boundary is explicit rather than implicit.  If the whole
center is one large-supported aggregate `q=S`, its owner lift gives
`S^2<=7n`.  But `S=2n+d+k+1>2n`, while the equation gives `n>9d` and hence
`n>=2`; therefore `S^2>(2n)^2>7n`, a contradiction.  The narrower
one-prime-power surface

```text
no_four_solution_of_reflection_center_one_large_prime_power
```

is also banked directly.

## Explicit small-prime loss bound

The small-prime branch now has a uniform quantified restriction.  For any
prime `p` (including `p<=k`) define

```text
E_p = v_p(S),
ell_p = v_p(reflectionCoeff(k)) + v_p((k-1)!),
h_p = p^(E_p-ell_p).
```

Then every exact target-range equation satisfies

```text
h_p <= k-1
  or
h_p^2 <= (k-1)! * 7n.                            (3)
```

The first alternative is exactly the non-reflected owner case: `h_p` divides
the nonzero owner offset, whose absolute value is at most `k-1`.  In the
reflected case, the uncancelled weighted square lift gives
`h_p^2 | C_i Z_i`, with `C_i | (k-1)!`, `0<|Z_i|<=7n`, proving the second
alternative.  Restoring the complete exponent gives the single explicit
bound

```text
p^(2E_p) <= p^(2ell_p) * ((k-1)^2 + (k-1)! * 7n).   (4)
```

The kernel surfaces are

```text
center_residual_power_small_or_weighted_square_bound
center_prime_power_sq_le_with_explicit_reflection_loss.
```

Both report exactly `[propext, Classical.choice, Quot.sound]`.  Bound (4)
does not by itself control the product over all small bases; it is a proper
restriction, not a disguised statement of Target 2.

## Reflected next-order identity

The next cofactor term has also been derived and exact-arithmetic tested.
Write `A=n+i=hx`, `S=A+B=hm`, and let `C_i,D_i` be the constant and linear
coefficients of the local cofactor at owner `i`.  Assuming the reflected
owner landing and the quadratic residual, the exact equation implies

```text
even k:  m+3x = h a  ->  h | C_i*a - 12*D_i*x^2,
odd k:   5x-m = h a  ->  h | C_i*a + 20*D_i*x^2.  (5)
```

The signs and constants come from reflecting the cofactor itself:
`Q_{k+1-i}(B)=(-1)^(k-1)Q_i(-B)`.  Keeping
`Q_i(z)=C_i+D_i z (mod h^2)` shows, uniformly in both parities, that

```text
equationError + h^2 * obstruction = 0 (mod h^3).
```

The exact verifier checks 66,910 rows with no floating point and keeps the
failed quadratic premise explicit on the synthetic `1489/4271` reflected
fixtures.  Identity (5) is not yet a public Lean surface, so it is recorded
as the next formalization node rather than counted as kernel-banked progress.

## Proof

For an owner `i`, write

```text
C_i = product_{1<=r<=k, r!=i} (r-i)
    = (-1)^(i-1) (i-1)! (k-i)!.
```

More generally, suppose a positive integer `h` divides both a lower owner
`A=n+i` and an upper owner `U=n+d+j`.  Remove those factors from the two
block products.  The remaining lower cofactor is congruent to `C_i` modulo
`h`, while the remaining upper cofactor is congruent to `C_j` modulo `h`.
Multiplication by `A` and `U`, respectively, upgrades both cofactor errors to
multiples of `h^2`.  The exact equation then gives

```text
h^2 | C_j U - 4 C_i A.                            (3)
```

This argument uses the full product equality.  A row prefix or reflection
congruence alone does not imply (3).

For the reflected upper index `j=k+1-i`, direct factorial reflection gives

```text
C_{k+1-i} = (-1)^(k-1) C_i.
```

Hence (3) becomes

```text
h^2 | C_i * ((-1)^(k-1)B - 4A).                  (4)
```

If `h=p^e` and `p>=k`, then `p` divides neither `(i-1)!` nor `(k-i)!`.
Cancelling `C_i` in (4) proves (1).

It remains to obtain the reflected landing with the complete exponent
`e=v_p(S)`.  The banked owner-correlation theorem supplies exponent

```text
v_p(S) - v_p(reflectionCoeff(k)) - v_p((k-1)!).
```

For `p>k>=16`, both subtracted valuations are zero.  Its owner offset is
divisible by `p^e`.  A nonzero offset has absolute value at most `k-1`, while
`p^e>=p>k`; therefore the offset is zero and `j=k+1-i`.  This proves the
hypotheses of (1).

Finally, the banked ratio inequality gives `9d<n`.  If `k` is even, the
absolute value in (1) is

```text
B+4A = 5n+d+k+1+3i <= 7n.
```

If `k` is odd, it is

```text
4A-B = 3n-d-k-1+5i <= 7n,
```

and the same inequality `9d<n`, together with `i<=k<=d`, makes this value
strictly positive.  A nonzero multiple of `q^2` has absolute value at least
`q^2`, proving (2).

## Exact hostile fixtures

The independent verifier imports none of the producer implementation.

- `(984,3177026,4480)` still passes rows `1..16` and fails row `17`.  It is
  not an equation and its large center prime `706613` has no reflected owner
  landing, so the new theorem cannot be invoked.
- `(244,48502,277)` still passes rows `1..15` and fails row `16`.  It is not
  an equation and has no center prime above `k`.
- The first-order reflected synthetic point `(984,3177027,4480)` has the
  reported pairs `(1489,499,486)` and `(4271,597,388)`, but the new linear
  residues modulo the prime squares are `1844871` and `2349050`, both
  nonzero.
- The even synthetic reflected pair `(p,i)=(59,7)` has residue `2655 mod
  59^2`.
- The odd synthetic reflected pairs for `p=19,31,41,43` have residues
  `228,496,1107,1118` modulo their prime squares.

These failures are required: all seven points fail the exact equation.  They
show that the new quadratic conclusion is not silently inferred from the
older first-order reflection package.

The two `d=1` telescopes `(9,2,1)` and `(15,4,1)` satisfy the generic
weighted lift.  They remain outside the target domain `d>=k`.

## Exact remaining gap

The first theorem does **not** prove that `S` has a dominant prime power.
The aggregate theorems eliminate every no-small-prime center whose complete
large components occupy at most two reflected owners.  Thus any remaining
hypothetical solution has a center satisfying

```text
forall p prime, p>k and p|S
  -> (p^v_p(S))^2 <= 7n,
```

together with at least one prime divisor at most `k`, or at least three
distinct reflected owners carrying its large prime-power components.  (The
branches may overlap.)  In the small-prime branch, (3) and (4) apply to every
base with the exact loss shown.  Eliminating these mixed/at-least-three-owner
factorizations still requires a global correlation among three reflected
owner buckets or between the large buckets and the small-prime part.
Replacing that missing correlation
by the assertion that some center power exceeds `sqrt(7n)` would be false
for generic smooth integers and is not counted as a reduction of Target 2.

A global cleaning by a fixed loss `g` does not directly reduce to the
`S=qr` core: with `S=gqr`, the even multiplier window becomes
`5g^2<uv<8g^2` (and the coefficient-one identities sharpen the upper side to
`4uv<25g^2`), while the odd window becomes `g^2<uv<4g^2`.  These intervals
contain many integers when `g>1`.  Any global-loss aggregation must therefore
retain (5), the owner indices, or another next-order constraint; merely
dropping `g` would be unsound.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_t2_smooth_rows

lake env lean ErdosProblems/Erdos686ReflectedAlignmentSquareLift.lean
lake env lean ErdosProblems/Erdos686ReflectedAlignmentTwoFactor.lean
```

The producer checks 127,288 exact congruence rows.  The independent hostile
grid checks 109,133 more.  The two-factor tests add 27,252 exact product
window rows, 26,136 target-range centers, 9,348 two-owner aggregate centers,
3,020 one-component centers, and 11,284 exact loss decompositions.  The
independent implementation adds 14,616 window rows, 15,456 centers, 801
oriented large factor pairs (108 with fully large-supported aggregates), and
2,680 one-component centers.  The reflected next-order verifier adds 66,910
exact cubic-congruence rows.
Neither finite grid is used to prove a universal theorem; the universal
proofs are the Lean derivations above.
