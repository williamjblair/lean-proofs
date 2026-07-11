# Hostile audit: Erdős 686 global two-prime closure

Status: **PASS for the exact two-distinct-prime-support slice.**  The final
endpoint builds, has the claimed theorem surface, stays inside the kernel
axiom allowlist, and survives independent exact-arithmetic reproduction.
This does not address gaps with at least three distinct prime divisors.

This audit is independent of the producer.  The producer modules are treated
as untrusted inputs.  The independent verifier imports no producer Python
code and recomputes the finite arithmetic from definitions.

## Frozen inputs and build history

The accepted frozen inputs are:

```text
Erdos686GlobalResidualConcentration.lean
  495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24
Erdos686GlobalResidualTwoPrime.lean
  ca1a59a8e3cef454d9255a8fd70dff3d7c516492bd4c379b097e711ef24c060d
Erdos686TwoPrimeSecondLift.lean
  e4ec6011fa24122072aa35ddba80e12d8d7ab0f9cd37a290610a3b2e4d493dbd
producer verifier
  86f36568088cb8e093e0f2b69db9da9aa1fb587dda0f03171af44082cd609d9a
producer tests
  dcc44b555bc6fe6b98e5e99c90da2fba40518d24e6aad9fb063c2dfe22323507
producer findings
  06933feb77a7d90c1dd2eccd6681645557eb1ce36e9da1b08586271a962c1742
independent hostile verifier
  e0b2b9b789988726e5e65f66cf95a9f9719abfd05d47c7b8e1cb75471e6b09ac
independent hostile tests
  63e86d4e6cf3b4ab0347b054fab1509fa38c419161356c2c8de72965e2cd52f0
```

The concentration module independently compiled from source to fresh files
under `/tmp` (1.4 MiB `.olean`, 59 KiB `.ilean`).  Its seven novel public
surfaces all reported exactly
`[propext, Classical.choice, Quot.sound]`.

The first composition SHA
`2aa35ba29eaeb23eec5e15cfe03042632ac7f0a66519f509ee032750fb3e482c`
did **not** pass: after duplicate jobs were
consolidated to one clean compiler process, Lean consumed about 2.7 GiB and
terminated without emitting an `.olean`.  The failure localized to the giant
60-leaf normalization in `localThirdQuadratic_eq_table`.

The accepted SHA replaces that normalization with a proved recursive
integer coefficient accumulator and 60 ordinary kernel `decide` leaves.
The consolidated build then passed `[8256/8256]` in 39 seconds and emitted a
6.4 MiB `.olean` plus a 127 KiB `.ilean`.  An independent replay/no-op build
also passed all 8,256 jobs.  The failed SHA is retained here as audit history;
no claim relies on it.

## Dependency tree

The claimed endpoint is

```text
two_prime_support_below_cutoff_of_global_residual_lifts
```

with exact structural hypotheses

```text
p,q prime; p != q; e,f > 0;
k in {5,7,9,11,13,15};
d = p^e q^f;
B(k,n+d) = 4 B(k,n);
n+1 < C d; A = 3C+2; A <= 35.
```

The last three numerical premises are already banked row-window consequences
with `(C,A)=(4,14),(5,17),(7,23),(8,26),(9,29),(11,35)`.  They are not a new
tail-strength assumption.

```text
endpoint
|- primePower_component_exists_globalResidual_clean (twice)
|  |- gap_sq_dvd_globalLocalResidualNat_product
|  |- p != 3 maximum-valuation concentration
|  `- p = 3 exact common-factor reduction
|- globalResidual_prime_loss_factor_le (twice)
|- localResidual_pos_lt_of_base_bound (twice)
|- same owner
|  `- coprime square product plus X_i < A d
`- distinct owners
   |- exists_positive_local_coefficient (twice)
   |- coefficient_product_lt
   |- exact Pell subtraction aP^2-bQ^2=3(i-j)
   |- second_order_local_lift (twice)
   |- third_order_local_lift (twice)
   `- two_clean_residual_buckets_below_cutoff
      |- clean_second_obstruction_divisibilities
      |- target_local_taylor_bounds
      |- one second obstruction nonzero
      |  `- d < A (10^30)^2 g^6
      `- both second obstructions zero
         |- clean_third_zero_component_dvd (twice)
         |- nonzero quadratic coefficients
         `- d < 400 (10^12)^2 35^2 g^9
```

There is no use of a determinant-nonvanishing certificate in the endpoint.
Reflected simultaneous zeros are admitted and enter the cubic branch.

## Independent exact arithmetic

Files:

```text
compute/campaign686/global_two_prime_hostile_verify.py
compute/campaign686/test_global_two_prime_hostile_verify.py
```

The independent suite reports `10 passed`; together with the producer suite,
the final run reports `19 passed`.  It reproduces:

- all 60 owner coefficient triples directly from
  `product_{j != i}(X+j-i)`;
- exact agreement with all 60 second-coefficient, third-coefficient, and
  erased-index Lean table entries;
- maximum absolute coefficients
  `87,178,291,200`, `283,465,647,360`, and `392,156,797,824`, each strictly
  below `10^12`, with all 60 quadratic coefficients nonzero;
- 60 same-owner cases and 610 ordered distinct-owner cases, including 108
  center-touching pairs;
- 556 nondegenerate ordered pairs and all 54 reflected simultaneous-zero
  ordered pairs.  Every zero pair has an independently constructed exact
  positive integral `(g,ab)` witness, so this branch is not discarded;
- all 610 sharper second-obstruction pair bounds, including the exact maximum
  `217044647287343042885059609316395849093627507558461004041714015187255309475392782336000000000`,
  and all 27 unordered reflected cubic bounds, including the exact maximum
  `93984078683194682557325451381987070845762855139556197071318510982175649195251213580361531392000000000`;
- 2,100 signed cubic-remainder checks and 15,420 independent checks of the
  exact coefficient-20 congruence modulo `h^2`;
- exact row loss products
  `108,1620,136080,1224720,242494560,18914575680`;
- exact `p=2` and `p=3` worst losses `64` and `59049`, and the valid loose
  two-component cofactor bound
  `g <= 59049^2 = 3,486,784,401`;
- 1,014 ordered `(p,q)=(2,3),(3,2)` exponent decompositions, including cases
  where either cleaned component equals one;
- 22,187 independently selected positive global-square premises, with
  42,400 cleaned components: 15,653 for `p=2`, 13,908 for `p=3`, 1,002 where
  their owners coincide, 7,776 where they differ, and 4,830 center owners.

The exact uniform cutoff integers are:

```text
same owner:
  35*(59049^2)^2
  = 425518291066992508035 < 10^120

nonzero second obstruction:
  35*(10^30)^2*(59049^2)^6
  = 62895360497005092364461294032836176390601646963824788724035000000000000000000000000000000000000000000000000000000000000
  < 10^120

both second obstructions zero:
  400*(10^12)^2*35^2*(59049^2)^9
  = 37326900542474532246251966583101625257708152687173646394760767215028997298086188629604490000000000000000000000000000
  < 10^120.
```

The second-obstruction coefficient before multiplication by `g^2` is
`3,855,000,000,000,000 < 10^30`, with exact margin
`999,999,999,999,996,145,000,000,000,000`.

## Boundary and falsification checks

- `p=2` uses the unit-step branch because `gcd(2,3)=1`; its maximal loss is
  exactly `2^6=64` at `k=15`.
- `p=3` is separately reduced by
  `X_i=3(n-d/3+i)`.  The `t=0` boundary makes all retained divisibilities
  unit divisibilities, while `c_3(k)>0` still gives `t<=e-1` for division of
  `d/3`.
- Cleaned powers can equal one.  Positivity, coprimality, the same-owner
  product, and both local-lift interfaces remain valid in that boundary.
- Same owner is not silently forced distinct: the endpoint combines the two
  coprime square divisors directly.
- Distinct center owners are included among the 610 ordered cases; the cubic
  coefficient at every center is independently nonzero.
- Simultaneous second-order zeros are real (54 ordered exact witnesses) and
  are repaired by the third lift rather than excluded.
- The `d=1` telescopes lie outside `d>=10^120` and have no two-positive-
  exponent prime support.
- The named large-`k` row-prefix fixtures are outside the six rows and are not
  full equation solutions; neither is used as a contrary premise.

## Final kernel gate

All gates pass on the accepted frozen SHA:

1. clean consolidated build and independent replay both complete all 8,256
   jobs and emit the target object;
2. standalone `#check` shows the endpoint exactly as stated in the dependency
   section, including `d=p^e*q^f`, distinct primality, positive exponents,
   the exact block equation, and only the banked row-window premises;
3. `#print axioms` on the endpoint and each of the eight novel public
   dependencies reports exactly
   `[propext, Classical.choice, Quot.sound]`;
4. a comment-aware code-token scan across the concentration, second-lift, and
   composition sources finds no `sorry`, `admit`, `native_decide`, `axiom`,
   or `unsafe` declaration.  Every private declaration is a proved lemma or a
   definition, not an assumption;
5. producer and independent suites pass together: `19 passed in 1.41s`.

## Verdict and exact scope

**PASS.**  Under the already verified row-window bounds, every exact solution
in one of the six odd rows whose gap has exactly two distinct prime divisors

```text
d = p^e q^f,  p and q distinct primes,  e,f > 0
```

satisfies `d < 10^120`.  This removes the entire remaining small-prime
two-support slice; neither `p>=k` nor `q>=k` is assumed.  The proof covers
`p=2`, `p=3`, unit cleaned components, coincident owners, distinct center
owners, and simultaneous second-obstruction zeros.  The exact remaining
odd-tail support gap is the at-least-three-distinct-prime case; this audit
does not claim a proof of that case or of full Target 1.
