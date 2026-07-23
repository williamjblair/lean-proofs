import Research.FiberTypes

namespace Erdos796

/-- A finite capacity profile of pairwise cross-compatible core types. -/
structure FiberProfile (R : ℕ) where
  posR : 0 < R
  fiber : Fin R → Finset ℕ
  positive : ∀ j d, d ∈ fiber j → 0 < d
  bounded : ∀ j d, d ∈ fiber j → d ≤ j.val + 1
  compatible : ∀ i j, CrossCompatible (fiber i) (fiber j)

namespace FiberProfile

/-- Type chosen by a profile for capacity `J`. -/
def base {R : ℕ} (P : FiberProfile R) (J : ℕ) : Finset ℕ :=
  P.fiber ⟨min (J - 1) (R - 1), by have := P.posR; omega⟩

/-- The chosen base type lies in `[1,R]`. -/
theorem base_subset {R : ℕ} (P : FiberProfile R) (J : ℕ) :
    P.base J ⊆ Finset.Icc 1 R := by
  intro d hd
  have hpos := P.positive _ d hd
  have hle := P.bounded _ d hd
  exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩

/-- At positive capacity, the base type is available. -/
theorem base_le_capacity {R J d : ℕ} (P : FiberProfile R)
    (hJ : 0 < J) (hd : d ∈ P.base J) : d ≤ J := by
  have hle := P.bounded ⟨min (J - 1) (R - 1), by have := P.posR; omega⟩ d hd
  change d ≤ min (J - 1) (R - 1) + 1 at hle
  omega

/-- Extend the base type by every prime above `R` through capacity `J`. -/
def extended {R : ℕ} (P : FiberProfile R) (J : ℕ) : Finset ℕ :=
  primeExtendType R J (P.base J)

/-- The base type and the adjoined prime tail are disjoint, so extended-fiber
cardinality splits exactly. -/
theorem extended_card {R : ℕ} (P : FiberProfile R) (J : ℕ) :
    (P.extended J).card = (P.base J).card +
      ((Finset.Icc (R + 1) J).filter Nat.Prime).card := by
  unfold extended primeExtendType
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro d hdBase hdPrime
  have hdle := (Finset.mem_Icc.mp (P.base_subset J hdBase)).2
  have hdgt := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hdPrime)).1
  omega

/-- Every member of an extended fiber is positive. -/
theorem extended_positive {R J d : ℕ} (P : FiberProfile R)
    (hd : d ∈ P.extended J) : 0 < d := by
  rcases Finset.mem_union.mp hd with hdBase | hdPrime
  · exact (Finset.mem_Icc.mp (P.base_subset J hdBase)).1
  · have hdLower := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hdPrime)).1
    omega

/-- Extended fibers at arbitrary capacities remain cross-compatible. -/
theorem extended_compatible {R : ℕ} (P : FiberProfile R) (J L : ℕ) :
    CrossCompatible (P.extended J) (P.extended L) := by
  apply primeExtendType_crossCompatible
  · exact P.base_subset J
  · exact P.base_subset L
  · exact P.compatible _ _

/-- At positive capacity, the entire extended fiber is available. -/
theorem extended_le_capacity {R J d : ℕ} (P : FiberProfile R)
    (hJ : 0 < J) (hd : d ∈ P.extended J) : d ≤ J := by
  rcases Finset.mem_union.mp hd with hdBase | hdPrime
  · exact P.base_le_capacity hJ hdBase
  · exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hdPrime)).2

/-- The all-`n` construction attached to a certified finite profile. -/
def construction {R : ℕ} (P : FiberProfile R) (n : ℕ) : Finset ℕ :=
  heterogeneousLift (sqrtPrimeLabels n) n.sqrt
    (fun q => P.extended (n / q))

/-- The exact profile-construction cardinality is the sum of its fiber sizes. -/
theorem construction_card_eq_sum {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    (P.construction n).card =
      ∑ q ∈ sqrtPrimeLabels n, (P.extended (n / q)).card := by
  apply heterogeneousLift_card_eq_sum
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqIcc := Finset.mem_Icc.mp hq'.1
    exact ⟨by omega, hq'.2⟩
  · intro q hq d hd
    exact Finset.mem_Icc.mpr
      ⟨P.extended_positive hd,
        le_trans (P.extended_le_capacity (Nat.div_pos
          (Finset.mem_Icc.mp (Finset.mem_of_mem_filter q hq)).2
          (Finset.mem_filter.mp hq).2.pos) hd) (div_label_le_sqrt hq)⟩

/-- Exact decomposition of a profile construction into finite-profile and
prime-tail incidence counts. -/
theorem construction_card_decomposition {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    (P.construction n).card =
      (∑ q ∈ sqrtPrimeLabels n, (P.base (n / q)).card) +
      ∑ q ∈ sqrtPrimeLabels n,
        ((Finset.Icc (R + 1) (n / q)).filter Nat.Prime).card := by
  rw [P.construction_card_eq_sum n]
  simp_rw [P.extended_card]
  exact Finset.sum_add_distrib

/-- Every profile construction satisfies the representation bound. -/
theorem construction_hasRepBound {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    HasRepBound 3 (P.construction n) := by
  apply heterogeneousLift_hasRepBound
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqIcc := Finset.mem_Icc.mp hq'.1
    exact ⟨by omega, hq'.2⟩
  · intro q hq r hr
    exact P.extended_compatible (n / q) (n / r)

/-- Every profile construction is contained in the target interval. -/
theorem construction_subset_Icc {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    P.construction n ⊆ Finset.Icc 1 n := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨⟨q, d⟩, hqd, rfl⟩
  have hqd' := Finset.mem_filter.mp hqd
  have hq : q ∈ sqrtPrimeLabels n := (Finset.mem_product.mp hqd'.1).1
  have hdIcc : d ∈ Finset.Icc 1 n.sqrt := (Finset.mem_product.mp hqd'.1).2
  have hdFiber : d ∈ P.extended (n / q) := hqd'.2
  have hq' := Finset.mem_filter.mp hq
  have hqIcc := Finset.mem_Icc.mp hq'.1
  have hJpos : 0 < n / q := Nat.div_pos hqIcc.2 hq'.2.pos
  have hdle : d ≤ n / q := P.extended_le_capacity hJpos hdFiber
  have hmul : q * d ≤ n := by
    simpa [Nat.mul_comm] using Nat.mul_le_of_le_div q d n hdle
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hq'.2.pos (Finset.mem_Icc.mp hdIcc).1, hmul⟩

/-- Exact extremal lower bound from every certified profile. -/
theorem construction_card_le_g {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    (P.construction n).card ≤ g 3 n := by
  classical
  unfold g
  apply Finset.le_sup
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (P.construction_subset_Icc n),
    P.construction_hasRepBound n⟩

end FiberProfile
end Erdos796
