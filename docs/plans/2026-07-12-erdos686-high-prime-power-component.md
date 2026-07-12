# Erdős 686 high prime-power component Lean plan

## Target

Formalize the audited GPT-Pro trichotomy for a canonical component
`e=d.factorization p`, `q=p^e>=k`.  Put

```text
lambda = Nat.log p (k-1)
mu = min lambda (e-2).
```

The three public lift gates should produce residual divisors

```text
p>=5: p^(2e-lambda)
p=2:  2^(2e-lambda+2)
p=3:  3^(2e-mu-1).
```

A generic positive-residual ceiling then gives exactly the no-solution
thresholds `6`, `24`, and `6` from the audited packet.

## Existing infrastructure to reuse

- `exists_blockProduct_factorization_concentration` for a maximum-valuation
  owner;
- `unique_dvd_add_of_mem_Icc_of_le` with the composite modulus `p^e`;
- `four_blockProduct_eq_implies_oddBlock_eq` for the `p=2` unit product;
- `nine_mul_gap_lt_n_of_four_solution` for positivity;
- `eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution` for the
  residual ceiling;
- Mathlib `ordProj_mul_ordCompl_eq_self`, `not_dvd_ordCompl`,
  `factorization_prod_apply`, `Nat.ModEq.of_dvd`, coprime cancellation, and
  `padicValNat_le_nat_log`.

Do not route through the existing local-coefficient quadratic lift: it loses
the factorial valuation and cannot recover the logarithmic loss `lambda`.

## Required private helpers

1. A generic `p`-free block/cofactor product using `ordCompl[p]`, including
   the exact quotient-four equation.
2. Translation valuation:
   `v_p(x)<e -> v_p(x+d)=v_p(x)` and
   `v_p(x)>e -> v_p(x+d)=e`.
3. The corresponding unit congruence modulo `p^(e-v_p(x))`.
4. Nonowner cofactor-product congruence modulo `p^(e-lambda)`.
5. The owner unit identity when the lower and upper valuations are known.
6. For `p=3`, if no `3^e` owner exists, the terms of valuation `e-1` have
   cardinality at most two.  In the two-term case the normalized residues are
   `1,2 mod 3`, contradicting the exact mod-nine unit equation.

The last item is the largest engineering block; it needs explicit
Finset/cardinality and ordered-index plumbing but no new number-theoretic
input.

## Case split

- `p>=5`: exclude maximum valuation below `e` by the unit-product equation
  modulo `p`, and above `e` by the total valuation sum.  Thus the maximum is
  exactly `e`; the cofactor congruence yields
  `p^(e-lambda) | 3a-m`.
- `p=2`: total valuation must increase by exactly two.  The maximum is `e`
  and the upper owner has valuation `e+2`; the odd-unit equation supplies the
  extra power of four.
- `p=3`: exclude maximum above `e`, at most `e-2` modulo nine, and equal to
  `e` modulo three.  The cardinality-two helper forces a single
  valuation-`e-1` owner, giving `3^(e-mu-1) | a-m`.

Before every natural truncated-subtraction rewrite, prove `lambda<e`; every
factorization lemma also needs the relevant term nonzero.  The theorem must
take the exact valuation equality, not merely `p^e|d`.

The Nair--Shorey short strip is independent, external, and remains
paper-only.
