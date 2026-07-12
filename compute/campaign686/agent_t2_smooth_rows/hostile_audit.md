# Hostile audit: reflected-alignment square lift

Verdict: **PASS as a strict equation-level strengthening of the banked
reflection-owner alternative.  FAIL as a complete Target 2 closure.**

## Dependency tree

```text
exact equation B(k,n+d)=4B(k,n)
|
+- local factorization at lower owner i
|  `- cofactor = C_i (mod h)
|
+- local factorization at upper owner j
|  `- cofactor = C_j (mod h)
|
+- h divides both owner terms
|  `- both cofactor errors acquire a second factor h
|
`- reflected index j=k+1-i
   +- C_j=(-1)^(k-1) C_i
   `- for p>=k, p does not divide C_i

large-center specialization
|
+- banked reflection-owner correlation
|  `- p^v_p(S) lands on lower and upper owners for p>k>=16
+- offset divisibility and |offset|<=k-1
|  `- p>k forces reflected alignment
`- banked 9d<n ratio bound
   `- nonzero parity linear has absolute value at most 7n
```

No node invokes `LargeKSmoothHypothesis`, a fixed row-prefix assertion, or a
theorem equivalent to Target 2.

## Per-node verdicts

| Node | Verdict | Evidence |
|---|---|---|
| Matched-owner `h^2` lift | PASS | `matched_owner_local_coefficients_dvd_sq`; 236,421 combined exact grid rows. |
| Reflected coefficient identity | PASS | kernel proof from the closed factorial formula. |
| Prime cancellation for `p>=k` | PASS | banked `prime_not_dvd_localBlockCoefficientNat`. |
| Full center exponent for `p>k>=16` | PASS | coefficient and factorial valuations both reduce to zero in Lean. |
| Reflected alignment | PASS | nonzero offset is in `[1,k-1]`, incompatible with divisibility by `p^e>=p>k`. |
| Uniform `q^2<=7n` | PASS | parity split plus the exact banked `9d<n` inequality. |
| Dominant center power exists | **NOT PROVED** | false for generic balanced smooth integers; no such premise is introduced. |
| Target 2 | **OPEN** | balanced center factorization across multiple reflected owners remains. |

Every phrase such as “too large” is resolved by the exact condition

```text
(p^v_p(S))^2 > 7n.
```

Under that quantified condition the equation is impossible; without it, the
audit makes no closure claim.

## Frozen source hashes

```text
228674048860d7098222ea885bd3937a3732a2a109c24f113445d3ad5c40deba  ErdosProblems/Erdos686ReflectedAlignmentSquareLift.lean
d00c559276e64f0f74d8ec1ff97520fb78d413798f8b9487bf9e0d9b5aaca0f6  compute/campaign686/agent_t2_smooth_rows/reflected_alignment_square_lift.py
4632c9640cd9c0aac9c3d5c100184407129da48cd2fe4f27cccae16d0f918265  compute/campaign686/agent_t2_smooth_rows/test_reflected_alignment_square_lift.py
d2ad2e1bbb1ce5f63511b9017a4b386871af6846e43c82a8c81f9f919eb66c76  compute/campaign686/agent_t2_smooth_rows/reflected_alignment_square_lift_hostile_verify.py
dcdf211a02115c405c63520ae416d87c575bee21d5d4735f3a67da7143ae0051  compute/campaign686/agent_t2_smooth_rows/test_reflected_alignment_square_lift_hostile_verify.py
```

Hashes record the pre-report source snapshot.  Regenerate them after any
edit and update this table before integration.
