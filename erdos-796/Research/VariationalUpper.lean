import Research.TruncatedTypes
import Research.Profiles

namespace Erdos796

/-- Real layer weight for a capacity profile. -/
noncomputable def profileLayerWeight {R : ℕ} (i : Fin R) : ℝ :=
  if i.val + 1 = R then (1 : ℝ) / R
  else (1 : ℝ) / ((i.val + 1) * (i.val + 2) : ℕ)

/-- Finite variational objective of one compatible profile.  This telescoping
form has coefficient `1/(m(m+1))` at every capacity `m`, followed by the
terminal correction `1/(R+1)`; hence the total last-layer coefficient is
`1/R`. -/
noncomputable def FiberProfile.beta {R : ℕ} (P : FiberProfile R) : ℝ :=
  (∑ i : Fin R,
      ((P.fiber i).card : ℝ) /
        (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) +
    ((P.fiber ⟨R - 1, by have hR := P.posR; omega⟩).card : ℝ) / (R + 1)

/-- Reciprocal-prime baseline through the profile cutoff. -/
noncomputable def primeMass (R : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE R, (1 : ℝ) / p

/-- Renormalized finite gain of a compatible profile. -/
noncomputable def FiberProfile.gamma {R : ℕ} (P : FiberProfile R) : ℝ :=
  P.beta - primeMass R

/-- Extend a positive-cutoff profile by one capacity.  The old last type is
extended by the new endpoint exactly when that endpoint is prime. -/
def FiberProfile.extendOne {R : ℕ} (P : FiberProfile R) : FiberProfile (R + 1) where
  posR := by omega
  fiber := fun i =>
    if h : i.val < R then P.fiber ⟨i.val, h⟩
    else primeExtendType R (R + 1)
      (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩)
  positive := by
    intro i d hd
    split at hd
    next h => exact P.positive ⟨i.val, h⟩ d hd
    next h =>
      rcases Finset.mem_union.mp hd with hold | hnew
      · exact P.positive ⟨R - 1, by have hR := P.posR; omega⟩ d hold
      · have hdI := Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hnew)
        omega
  bounded := by
    intro i d hd
    split at hd
    next h => exact P.bounded ⟨i.val, h⟩ d hd
    next h =>
      have hi : i.val = R := by omega
      rcases Finset.mem_union.mp hd with hold | hnew
      · have := P.bounded ⟨R - 1, by have hR := P.posR; omega⟩ d hold
        omega
      · have hdI := Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hnew)
        omega
  compatible := by
    intro i j
    split
    next hi =>
      split
      next hj => exact P.compatible ⟨i.val, hi⟩ ⟨j.val, hj⟩
      next hj =>
        have hSi : P.fiber ⟨i.val, hi⟩ ⊆ Finset.Icc 1 R := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨P.positive _ d hd, by
              have := P.bounded ⟨i.val, hi⟩ d hd
              omega⟩
        have hT : P.fiber ⟨R - 1, by have hR := P.posR; omega⟩ ⊆ Finset.Icc 1 R := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨P.positive _ d hd, by
              have := P.bounded ⟨R - 1, by have hR := P.posR; omega⟩ d hd
              omega⟩
        have hc := primeExtendType_crossCompatible R R (R + 1)
          (P.fiber ⟨i.val, hi⟩) (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩)
          hSi hT (P.compatible _ _)
        simpa [primeExtendType] using hc
    next hi =>
      split
      next hj =>
        have hS : P.fiber ⟨R - 1, by have hR := P.posR; omega⟩ ⊆ Finset.Icc 1 R := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨P.positive _ d hd, by
              have := P.bounded ⟨R - 1, by have hR := P.posR; omega⟩ d hd
              omega⟩
        have hTj : P.fiber ⟨j.val, hj⟩ ⊆ Finset.Icc 1 R := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨P.positive _ d hd, by
              have := P.bounded ⟨j.val, hj⟩ d hd
              omega⟩
        have hc := primeExtendType_crossCompatible R (R + 1) R
          (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩) (P.fiber ⟨j.val, hj⟩)
          hS hTj (P.compatible _ _)
        simpa [primeExtendType] using hc
      next hj =>
        have hS : P.fiber ⟨R - 1, by have hR := P.posR; omega⟩ ⊆ Finset.Icc 1 R := by
          intro d hd
          exact Finset.mem_Icc.mpr
            ⟨P.positive _ d hd, by
              have := P.bounded ⟨R - 1, by have hR := P.posR; omega⟩ d hd
              omega⟩
        exact primeExtendType_crossCompatible R (R + 1) (R + 1)
          (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩) (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩)
          hS hS (P.compatible _ _)

@[simp] theorem FiberProfile.extendOne_fiber_castSucc {R : ℕ}
    (P : FiberProfile R) (i : Fin R) :
    P.extendOne.fiber i.castSucc = P.fiber i := by
  simp [FiberProfile.extendOne, i.isLt]

@[simp] theorem FiberProfile.extendOne_fiber_last {R : ℕ}
    (P : FiberProfile R) :
    P.extendOne.fiber (Fin.last R) =
      primeExtendType R (R + 1)
        (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩) := by
  simp [FiberProfile.extendOne]

/-- Extending through the next endpoint adds exactly its primality indicator to
the terminal type cardinality. -/
theorem card_primeExtendType_succ (R : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 R) :
    (primeExtendType R (R + 1) S).card =
      S.card + if (R + 1).Prime then 1 else 0 := by
  have hnot : R + 1 ∉ S := by
    intro h
    have := (Finset.mem_Icc.mp (hS h)).2
    omega
  by_cases hp : (R + 1).Prime
  · rw [primeExtendType, Finset.Icc_self, Finset.filter_singleton, if_pos hp]
    simpa [hp] using Finset.card_union_of_disjoint
      (Finset.disjoint_singleton_right.mpr hnot)
  · rw [primeExtendType, Finset.Icc_self, Finset.filter_singleton, if_neg hp]
    simp [hp]

/-- One-step profile extension changes the variational objective by exactly the
new prime reciprocal. -/
theorem FiberProfile.beta_extendOne {R : ℕ} (P : FiberProfile R) :
    P.extendOne.beta = P.beta +
      (if (R + 1).Prime then (1 : ℝ) / (R + 1) else 0) := by
  have hS : P.fiber ⟨R - 1, by have hR := P.posR; omega⟩ ⊆
      Finset.Icc 1 R := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨P.positive _ d hd, by
        have := P.bounded ⟨R - 1, by have hR := P.posR; omega⟩ d hd
        omega⟩
  have hcard := card_primeExtendType_succ R
    (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩) hS
  have hnew (h : R < R + 1) :
      P.extendOne.fiber ⟨R, h⟩ = primeExtendType R (R + 1)
        (P.fiber ⟨R - 1, by have hR := P.posR; omega⟩) := by
    simp [FiberProfile.extendOne]
  unfold FiberProfile.beta
  rw [Fin.sum_univ_castSucc]
  simp only [FiberProfile.extendOne_fiber_castSucc,
    FiberProfile.extendOne_fiber_last, Nat.add_sub_cancel]
  rw [hnew, hcard]
  push_cast
  by_cases hp : (R + 1).Prime <;> simp [hp]
  all_goals
    have hR : (R : ℝ) + 1 ≠ 0 := by positivity
    have hR2 : (R : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- The reciprocal-prime baseline has the same one-step increment. -/
theorem primeMass_succ (R : ℕ) :
    primeMass (R + 1) = primeMass R +
      (if (R + 1).Prime then (1 : ℝ) / (R + 1) else 0) := by
  unfold primeMass
  rw [Nat.primesLE_succ]
  by_cases hp : (R + 1).Prime
  · rw [if_pos hp]
    simp [Nat.notMem_primesLE, hp, add_comm]
  · rw [if_neg hp]
    simp [hp]

/-- Prime extension preserves the renormalized finite gain exactly. -/
theorem FiberProfile.gamma_extendOne {R : ℕ} (P : FiberProfile R) :
    P.extendOne.gamma = P.gamma := by
  rw [FiberProfile.gamma, FiberProfile.gamma,
    FiberProfile.beta_extendOne, primeMass_succ]
  ring

end Erdos796
