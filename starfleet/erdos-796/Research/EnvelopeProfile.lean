import Research.GenericProfileAsymptotic

namespace Erdos796

section Envelope

variable {ι : Type*} [DecidableEq ι]

/-- Repeated types actually occurring in one capacity class. -/
def availableRepeatedTypes {R : ℕ} (I : Finset ι) (D : ι → Finset ℕ)
    (cap : ι → Fin R) (j : Fin R) : Finset (Finset ℕ) :=
  (repeatedTypes I D).filter fun T =>
    ∃ i ∈ I, cap i = j ∧ D i = T

/-- A cardinality-maximizing member of a finite family, or the empty type when
that family is empty. -/
noncomputable def maxCardType (A : Finset (Finset ℕ)) : Finset ℕ :=
  if h : A.Nonempty then
    Classical.choose (Finset.exists_max_image A Finset.card h)
  else ∅

lemma maxCardType_mem {A : Finset (Finset ℕ)} (hA : A.Nonempty) :
    maxCardType A ∈ A := by
  rw [maxCardType, dif_pos hA]
  exact (Classical.choose_spec
    (Finset.exists_max_image A Finset.card hA)).1

lemma card_le_maxCardType {A : Finset (Finset ℕ)}
    (hA : A.Nonempty) {T : Finset ℕ} (hT : T ∈ A) :
    T.card ≤ (maxCardType A).card := by
  rw [maxCardType, dif_pos hA]
  exact (Classical.choose_spec
    (Finset.exists_max_image A Finset.card hA)).2 T hT

lemma maxCardType_eq_empty {A : Finset (Finset ℕ)} (hA : ¬A.Nonempty) :
    maxCardType A = ∅ := by simp [maxCardType, hA]

/-- Pairwise-compatible fibers have one finite capacity profile that envelopes
every nonexceptional fiber cardinality in its own capacity class. -/
theorem exists_envelopeProfile {R : ℕ} (hR : 0 < R)
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R)
    (hpos : ∀ i ∈ I, ∀ d ∈ D i, 0 < d)
    (hbound : ∀ i ∈ I, ∀ d ∈ D i, d ≤ (cap i).val + 1)
    (hcompat : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → CrossCompatible (D i) (D j)) :
    ∃ P : FiberProfile R,
      ∀ i ∈ I, i ∉ exceptionalTypeIndices I D →
        (D i).card ≤ (P.fiber (cap i)).card := by
  classical
  let F : Fin R → Finset ℕ := fun j =>
    maxCardType (availableRepeatedTypes I D cap j)
  have hFrepeated : ∀ j : Fin R,
      F j = ∅ ∨ F j ∈ repeatedTypes I D := by
    intro j
    by_cases hA : (availableRepeatedTypes I D cap j).Nonempty
    · right
      exact (Finset.mem_filter.mp (maxCardType_mem hA)).1
    · left
      exact maxCardType_eq_empty hA
  have hFpos : ∀ j d, d ∈ F j → 0 < d := by
    intro j d hd
    by_cases hA : (availableRepeatedTypes I D cap j).Nonempty
    · have hmem := maxCardType_mem hA
      rcases (Finset.mem_filter.mp hmem).2 with ⟨i, hi, hcap, hDi⟩
      have hdDi : d ∈ D i := by
        change d ∈ maxCardType (availableRepeatedTypes I D cap j) at hd
        rw [hDi]
        exact hd
      exact hpos i hi d hdDi
    · have hempty : F j = ∅ := by
        exact maxCardType_eq_empty hA
      simp [hempty] at hd
  have hFbound : ∀ j d, d ∈ F j → d ≤ j.val + 1 := by
    intro j d hd
    by_cases hA : (availableRepeatedTypes I D cap j).Nonempty
    · have hmem := maxCardType_mem hA
      rcases (Finset.mem_filter.mp hmem).2 with ⟨i, hi, hcap, hDi⟩
      have hdDi : d ∈ D i := by
        change d ∈ maxCardType (availableRepeatedTypes I D cap j) at hd
        rw [hDi]
        exact hd
      have hle := hbound i hi d hdDi
      simpa [hcap] using hle
    · have hempty : F j = ∅ := by
        exact maxCardType_eq_empty hA
      simp [hempty] at hd
  have hFcompat : ∀ j k, CrossCompatible (F j) (F k) := by
    intro j k
    rcases hFrepeated j with hj | hj
    · simp [hj, CrossCompatible, crossMultiplicity]
    rcases hFrepeated k with hk | hk
    · simp [hk, CrossCompatible, crossMultiplicity]
    exact repeatedTypes_pairwise_compatible I D hcompat (F j) hj (F k) hk
  let P : FiberProfile R :=
    { posR := hR
      fiber := F
      positive := hFpos
      bounded := hFbound
      compatible := hFcompat }
  refine ⟨P, ?_⟩
  intro i hiI hiNotExceptional
  have hmult : 2 ≤ (typeFiber I D (D i)).card := by
    have hiSelf : i ∈ typeFiber I D (D i) :=
      Finset.mem_filter.mpr ⟨hiI, rfl⟩
    have hposcard : 0 < (typeFiber I D (D i)).card :=
      Finset.card_pos.mpr ⟨i, hiSelf⟩
    have hnle : ¬(typeFiber I D (D i)).card ≤ 1 := by
      intro hle
      exact hiNotExceptional (Finset.mem_filter.mpr ⟨hiI, hle⟩)
    omega
  have hrep : D i ∈ repeatedTypes I D := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i, hiI, rfl⟩, hmult⟩
  have hav : D i ∈ availableRepeatedTypes I D cap (cap i) := by
    exact Finset.mem_filter.mpr ⟨hrep, ⟨i, hiI, rfl, rfl⟩⟩
  have hA : (availableRepeatedTypes I D cap (cap i)).Nonempty := ⟨D i, hav⟩
  change (D i).card ≤ (F (cap i)).card
  exact card_le_maxCardType hA hav

end Envelope

end Erdos796
