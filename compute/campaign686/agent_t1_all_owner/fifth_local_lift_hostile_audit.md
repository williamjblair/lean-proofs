# Hostile audit: Erdős 686 fifth local lift

Date: 2026-07-12

## Claim under audit

The producer claims only the following necessary consequences:

1. the equation implies the exact fifth local obstruction modulo `H^4`;
2. three exact square residuals compose it to a cyclic obstruction modulo
   `P^4`;
3. naming the third quotient lifts the fourth quotient congruence to a
   congruence modulo `P^2`;
4. eliminating the cofactor product leaves the displayed coefficient
   `R5`, which is generically quadratic in the gap.

It does not claim that fifth order closes the three-owner branch.

## Dependency tree

```text
N0 polynomial Taylor remainder through coefficient 4
 |
 +-- N1 fifth_order_local_algebra
 |    inputs: exact residual identity and exact local block equation
 |
 +-- N2 fifth_order_local_lift
      inputs: actual factor, residual, and block equation

N3 exact product expansion
 B=(aP^2-3x)(aP^2-3y)
  =9xy-3a(x+y)P^2+a^2P^4
 |
 +-- N4 three_bucket_fifth_obstruction_dvd_fourth
 |    inputs: N1, N3, d=gPQR
 |
 +-- N5 target_three_bucket_fifth_obstruction_dvd_fourth
      inputs: N2 and actual step-three residuals

N6 cancel P^3 from a P^4 divisibility
 |
 +-- N7 squared third-quotient congruence modulo P^2

N8 exact polynomial elimination of t
 |
 +-- N9 reduced fixed-coefficient congruence modulo P^2
```

## Per-node verdicts

| node | verdict | independent check |
|---|---|---|
| N0 | PASS | Direct multiplication reconstructs `C,D,E,F,G`; 10,080 signed denominator identities satisfy the exact `81*T-G5=H^4*Q` formula. |
| N1 | PASS | Lean proves the integer algebra without division by `3`, `H`, or a coefficient. |
| N2 | PASS | The wrapper derives both Taylor remainders from the actual local cofactors and uses the actual block equation. |
| N3 | PASS | Direct expansion is checked in every one of 111,780 signed composition fixtures. |
| N4 | PASS | The independent verifier checks `(bc)^2*raw5-W5` modulo `P^4`; all remainders are zero. |
| N5 | PASS | Lean derives `x=i-j` and `y=i-l` from the supplied actual residual equations. |
| N6 | PASS | Cancellation assumes `P != 0` and cancels exactly `P^3`, with no primality assumption. |
| N7 | PASS | The quotient identity is checked exactly in the extended CRT fixture at all three cyclic owners. |
| N8 | PASS | Independent integer arithmetic checks the multiplier identity in all 111,780 signed fixtures. |
| N9 | PASS | Exact enumeration finds 6,156 nonzero and 54 zero gap-quadratic ordered views; the code and Lean use the same full polynomial. |

## Boundary and falsification matrix

| boundary | verdict | evidence |
|---|---|---|
| component `P=3` | PASS | 2,520 local denominator fixtures use `abs(H)=3`; 55,890 composition fixtures use `abs(P)=3`. No division by `3` occurs. |
| signed variables | PASS | 8,340 local and 97,892 composition fixtures contain negative input data. |
| unit opposite components | PASS | All 111,780 composition fixtures take `Q=R=1`; no nonunit assumption is hidden in the algebra. |
| quartic coefficient omitted | FAIL as required | 2,492 local fixtures acquire a nonzero remainder modulo `H^4` when the `340 G H^3 M^5` term is removed. |
| frozen 121-digit fourth fixture | FAILS fifth order | Each of the three local, composed, quotient, and reduced fifth remainders is nonzero for the frozen fourth representative. |
| fifth Hensel extension | PASS | Unit derivative `-81 C_i(d/P_i)^5 mod P_i` extends the same gap through fifth order at all three owners. |
| short upper window | OUT OF SCOPE | The extended fixture has residual-to-gap floor with 604 digits, so it fails `X_i<14d` by an explicit factor greater than `10^603/14`. |
| exact equation | OUT OF SCOPE | The extended block difference is nonzero, although divisible by each `P_i^6`. |
| `d=1` telescopes | PASS | `(k,n,d)=(9,2,1),(15,4,1)` remain exact equations but fail the required domain `k<=d`. |

## Packing audit

The new modulus is `P^2`, but the reduced fixed term has degree two in `d`
at 6,156 of 6,210 ordered views.  An absolute-value argument of the form

```text
0 < |729 C^2 bc z + R5 g^4| <= K g^4 d^2
```

implies only `P^2 <= K g^4 d^2`.  This is weaker than the already available
residual inequality `P^2 < A_k d` whenever `K g^4 d > A_k`; it cannot be
used as the missing fourth-power estimate.  No phrase such as “the fixed
term is small” is used: its exact degree and the 6,156/54 split are recorded.

The 54 center-reflected views have zero quadratic coefficient.  They are not
declared closed; they are the only subfamily for which a separate linear-gap
packing calculation is still warranted.

## Final verdict

PASS as a proper necessary fifth-order lift.  FAIL as a standalone closure
route: an explicit 121-digit Hensel/CRT family satisfies the full new package
with all third quotients nonzero while remaining outside the equation and
short-window hypotheses.
