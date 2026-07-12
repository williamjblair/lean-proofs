# FinalResidual integration snippet (do not count as a proof)

The exact Lucas conjunct for the large-row arm is:

```lean
(∀ p a : ℕ, p.Prime → 5 ≤ p → 0 < a → k = p ^ a - 1 →
  ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d)
```

It is a necessary restriction, not a contradiction.  In
`no_gap_solution_large_k_of_finalResidual`, derive it from the exact equation
as follows:

```lean
have hprimePowerBoundary :
    ∀ p a : ℕ, p.Prime → 5 ≤ p → 0 < a → k = p ^ a - 1 →
      ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d := by
  intro p a hp hp5 ha hkPow
  have hqeq :
      blockProduct (p ^ a - 1) (n + d) =
        4 * blockProduct (p ^ a - 1) n := by
    simpa [hkPow] using heq
  exact prime_power_pred_four_solution_endpoints_not_dvd hp hp5 hqeq
```

Append `hprimePowerBoundary` to the `Or.inr` tuple after adding the conjunct
to `FinalResidual686Hypothesis`.  The converse direction remains immediate:
`finalResidual_of_tail1000_and_smooth` uses only the first two large-arm
fields and needs no new proof step.

For completeness, the already kernel-passed component conjunct from the same
lane is:

```lean
(∀ p e : ℕ, p.Prime → 0 < e → k ≤ p → p ^ e ∣ d →
  6 * p ^ (2 * e) < (13 * k - 6) * d + 18 * (k - 1))
```

with derivation:

```lean
have hlargePrimeComponents :
    ∀ p e : ℕ, p.Prime → 0 < e → k ≤ p → p ^ e ∣ d →
      6 * p ^ (2 * e) < (13 * k - 6) * d + 18 * (k - 1) := by
  intro p e hp he hkp hpow
  exact large_prime_gap_component_square_strict_upper_of_four_solution
    hp he hk hd hkp hpow heq
```

This file is only an integration recipe.  The theorem modules and their axiom
reports are the auditable proof objects.
