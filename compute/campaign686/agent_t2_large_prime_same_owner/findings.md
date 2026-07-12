# Erdős 686 large-prime same-owner dominance

## Status

This lane is exact-arithmetic reproduced and kernel-checked.  The command
`lake env lean ErdosProblems/Erdos686LargePrimeSameOwner.lean` succeeds, and
all six public theorem gates print exactly
`[propext, Classical.choice, Quot.sound]`.  The source contains no placeholder
proof.

The independent exact verifier passes five focused tests and reports payload
SHA-256
`634ff9f4272299565eea5291c20e7583a50cfd7c50c4a863ff23c1356893eec1`.

## Duplication audit

The initially requested raw aggregation was already proved in a stronger
form.  In `Erdos686TwoOwnerGrouping.lean`,

`globalResidualGroupedLeft_square_dvd_residual`

states that the square of the product of every cleaned prime-power component
assigned to one owner divides that owner's positive local residual.  Its
proof already performs the pairwise-coprime finite-product aggregation.

For a prime `p>=k>=16`, the cleaned exponent is the full exponent.  Indeed
`p!=3`, `p` does not divide `(k-1)!`, and therefore

`globalResidualLossExponent p k = (0+1)/2 = 0`.

The odd-row theorem `two_large_prime_support_bounded_pell` also already
excludes equal owners for `k=2r+1` under its `A<k^2` package.  The new module
therefore does not re-prove either result.  Its genuinely new content is the
explicit large-row dominance link, its mixed-gap specialization, and the
all-parity `k>=16` wrapper.

## New generic dominance inequality

Write

`X_i = localResidual(n,d,i) = 3(n+i)-d`.

For an exact quotient-four solution with `k>=16`, `k<=d`, and
`i in [1,k]`, the already proved ratio ceiling gives

`18(n+1) < 13kd`.

If `h^2|X_i`, then `X_i>0` and `h^2<=X_i`.  Hence

```text
6h^2 + 6d
  <= 6X_i + 6d
   = 18(n+i)
  <= 18(n+1) + 18(k-1)
   < 13kd + 18(k-1).
```

Cancelling `6d` yields the strict necessary condition

`6h^2 < (13k-6)d + 18(k-1)`.                       (1)

The theorem `localResidual_square_strict_upper_of_four_solution`
formalizes exactly (1).  Applying the existing grouped-owner square divisor
gives

`6 H_i^2 < (13k-6)d + 18(k-1)`,

where `H_i` is the complete cleaned product assigned to owner `i`.
Consequently the opposite non-strict inequality

`(13k-6)d + 18(k-1) <= 6 H_i^2`                    (2)

is an explicit no-solution certificate.  This is a proper subclass: (2) is a
direct size comparison on a supplied owner bucket, not a reformulation of the
block equation.

## Mixed-gap two-component theorem

Let `p,q` be distinct primes, let `e,f>0`, and suppose

- `k>=16`, `k<=d`, `p,q>=k`;
- `p^e|d` and `q^f|d`;
- both full components divide the same lower factor `n+i`;
- `(13k-6)d+18(k-1) <= 6(p^e q^f)^2`.

Under an assumed block equation, the clean local square lift gives both
`(p^e)^2|X_i` and `(q^f)^2|X_i`.  Coprimality gives
`(p^e q^f)^2|X_i`, contradicting (1).  Extra prime factors of `d` are
allowed; only the displayed dominance comparison is required.

The theorem is

`no_four_solution_of_two_large_prime_components_same_owner_dominance`.

Its headline premise is equation-facing and natural: it takes the two actual
localization facts and derives the combined square divisor internally.

## Whole two-large-prime gap

If the two components comprise the whole gap,

`d=p^e q^f`,

then `d>=k^2`.  The dominance comparison is automatic:

```text
(13k-6)d + 18(k-1)
  <= (13k-6)d + 18d
   = (13k+12)d
  <= 6d^2,
```

because `13k+12<=6k^2<=6d` for `k>=16`.

Therefore an exact solution can only place the two full prime-power
components at distinct unique lower owners.  The theorem

`two_large_prime_whole_gap_has_distinct_local_owners`

states this for every parity of `k>=16`, includes exponent-one components,
and returns both clean square lifts.  It intentionally does not claim that
the surviving distinct-owner Pell branch is impossible.

## Exact reproduction

```sh
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_large_prime_same_owner/same_owner_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/agent_t2_large_prime_same_owner/test_same_owner_verify.py
```

Result: `5 passed in 0.09s`.  The verifier checks 41,625 exact parameter
tuples.  Its minimum dominance margin is 341,234 at the relaxed arithmetic
boundary `(k,p,e,q,f)=(16,16,1,16,1)`.

At the first distinct-prime boundary `(k,p,q,e,f)=(16,17,19,1,1)`,
`d=323`, the left side is 65,516 and `6d^2=625,974`, leaving margin 560,458.

Frozen source hashes:

- Lean source: `068e96884862222fb6d27c1ab19d0b9f3c42c3d0093ba2f820ff0e23b77a7611`;
- exact verifier: `629c437fe67dcb287bac9a7ef5030567cd4a30acb62b4c7cd1304f89bd606d65`;
- tests: `444c9ac6124015255c0d1363eb61a3ca921137b2147cde78c1dcb4654ae11d9c`.

Kernel status: **DIRECT-CHECK PASSED** with axioms exactly
`[propext, Classical.choice, Quot.sound]`.
