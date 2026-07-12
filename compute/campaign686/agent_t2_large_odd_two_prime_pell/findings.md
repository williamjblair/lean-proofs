# Erdős 686: uniform large-odd two-large-prime Pell package

## Status

This lane gives a new kernel-checked quantified restriction for every odd row
`k>=17`.  The command
`lake env lean ErdosProblems/Erdos686LargeOddTwoPrimePell.lean` succeeds, and
both theorem gates print exactly
`[propext, Classical.choice, Quot.sound]`.

The independent exact verifier passes six tests and reports payload SHA-256
`17ffe70274bcc4b7068be409f82da74e04de75563d5f1dfbdab4371389fcde5d`.

## Exact theorem

Let

```text
k = 2r+1 >= 17,
d = p^e q^f,
p,q distinct primes,
e,f > 0,
p,q >= k,
B_k(n+d) = 4 B_k(n).
```

Put `P=p^e`, `Q=q^f`, and

`A=3k+2`.

The theorem `large_odd_two_large_prime_pell_certificate` constructs
distinct indices `i,j in [1,k]` and positive integers `a,b` satisfying

```text
X_i = 3(n+i)-d = a P^2,
X_j = 3(n+j)-d = b Q^2,
aP < A Q,
bQ < A P,
ab < A^2,
aP^2-bQ^2 = 3(i-j).
```

It also returns the exact second-order divisibilities

```text
P | 3(C_i ab + 4D_i(i-j)),
Q | 3(C_j ab - 4D_j(i-j)),
```

where

```text
C_i = product_{1<=s<=k, s!=i}(s-i),
D_i = sum_{t!=i} product_{s!=i,t}(s-i).
```

If `i` is the center, the package additionally gives

`P^3|X_i` and `d<A^5`;

the symmetric statement holds when `j` is the center.

This is not a no-solution theorem for the distinct-owner branch.  It is an
explicit finite-coefficient generalized Pell reduction for every unbounded
odd row in the large-row regime.

## Why the uniform instantiation works

The new exact ratio window gives

`18(n+1)<13kd`.

Since `kd>0` and `13kd<18kd`, this implies the simple integral bound

`n+1<kd`.

Thus the existing theorem `two_large_prime_support_bounded_pell` applies with

```text
C=k,
A=3C+2=3k+2.
```

Its remaining side condition is automatic:

`3k+2<k^2` for every `k>=4`.

The imported large-row window starts at `k>=16`, so the first odd row in the
new wrapper is `k=17`.  There `A=53`, `A^2=2809`, and
`A^5=418195493`.

Repository search found no prior arbitrary-`r` instantiation.  Existing calls
to `two_large_prime_support_bounded_pell` occur only inside the six fixed-row
second-lift closure for `k=5,7,9,11,13,15`.

## Second-order zero branch

The second obstruction pair cannot be declared nonzero by coefficient signs
alone.  Exact algebra shows that a zero determinant forces reflection

`j=k+1-i`.

At a reflected pair with `i<j`, simultaneous zeros further force

```text
t=ab=4(k+1-2i) * sum_{s=i}^{k-i} 1/s.                 (Z)
```

The exact verifier checked 1,362,884 ordered owner pairs through odd `k=201`:
all 10,044 determinant-zero pairs were reflected.  It separately evaluated
(Z) for all 125,249 reflected pairs in odd rows `5<=k<=1001`; none was an
integer.  The smallest observed denominator was 3, at `(k,i)=(5,1)`, where
`t=100/3`.  The excluded boundary `k=3,i=1` does have the integral value
`t=12`.

This is evidence, not a uniform proof.  The exact remaining standalone lemma
for eliminating the simultaneous-zero branch is:

```text
For every odd k>=5 and 1<=i<(k+1)/2,
4(k+1-2i) * sum_{s=i}^{k-i} 1/s is not an integer.
```

No claim based on that lemma appears in the Lean theorem.

## Reproduction

```sh
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_large_odd_two_prime_pell/large_odd_pell_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/agent_t2_large_odd_two_prime_pell/test_large_odd_pell_verify.py
```

Result: `6 passed in 3.96s`.

Frozen hashes:

- Lean source: `15375f927b4f136b11c0d45223fe4016a1e7018890600cc7da72915fa82e1a7a`;
- exact verifier: `1e0f43cb96237a7e413c8aacdfa35b759a63e79dd490da587185d4b0cda5bdff`;
- tests: `9b31ac2f823fa11f7d3b947102dd8f6b78bcb063972634cc64eaace11e89520e`.

Kernel status: **DIRECT-CHECK PASSED** with axioms exactly
`[propext, Classical.choice, Quot.sound]`.
