import Research.UpperTruncation

namespace Erdos796

set_option maxHeartbeats 0

section PolynomialEnvelope

variable {ι : Type*} [DecidableEq ι]

/-- A non-self-compatible finite type has three distinct ordered
representations of one product. -/
theorem exists_three_self_representations
    {S : Finset ℕ} (hS : ¬ CrossCompatible S S) :
    ∃ m : ℕ, ∃ z₁ z₂ z₃ : ℕ × ℕ,
      z₁ ∈ S.product S ∧ z₂ ∈ S.product S ∧ z₃ ∈ S.product S ∧
      z₁.1 * z₁.2 = m ∧ z₂.1 * z₂.2 = m ∧ z₃.1 * z₃.2 = m ∧
      z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ := by
  have hmul : 2 < crossMultiplicity S S := Nat.lt_of_not_ge hS
  unfold crossMultiplicity at hmul
  rw [Finset.lt_sup_iff] at hmul
  rcases hmul with ⟨m, hm, hcount⟩
  unfold crossRepCount at hcount
  rw [Finset.two_lt_card] at hcount
  rcases hcount with ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, h₁₂, h₁₃, h₂₃⟩
  have hz₁' := Finset.mem_filter.mp hz₁
  have hz₂' := Finset.mem_filter.mp hz₂
  have hz₃' := Finset.mem_filter.mp hz₃
  exact ⟨m, z₁, z₂, z₃, hz₁'.1, hz₂'.1, hz₃'.1,
    hz₁'.2, hz₂'.2, hz₃'.2, h₁₂, h₁₃, h₂₃⟩

/-- A bundled three-pair certificate for failure of self-compatibility. -/
theorem exists_incompatibilityCertificate
    {S : Finset ℕ} (hS : ¬ CrossCompatible S S) :
    ∃ w : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)),
      w.1 ∈ S.product S ∧ w.2.1 ∈ S.product S ∧ w.2.2 ∈ S.product S ∧
      w.1.1 * w.1.2 = w.2.1.1 * w.2.1.2 ∧
      w.1.1 * w.1.2 = w.2.2.1 * w.2.2.2 ∧
      w.1 ≠ w.2.1 ∧ w.1 ≠ w.2.2 ∧ w.2.1 ≠ w.2.2 := by
  rcases exists_three_self_representations hS with
    ⟨m, z₁, z₂, z₃, hz₁, hz₂, hz₃, hp₁, hp₂, hp₃, h₁₂, h₁₃, h₂₃⟩
  exact ⟨(z₁, (z₂, z₃)), hz₁, hz₂, hz₃,
    hp₁.trans hp₂.symm, hp₁.trans hp₃.symm, h₁₂, h₁₃, h₂₃⟩

/-- Canonical three-pair certificate for failure of self-compatibility. -/
noncomputable def incompatibilityWitness (S : Finset ℕ) :
    (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact if h : ¬ CrossCompatible S S then
    Classical.choose (exists_incompatibilityCertificate h)
  else ((0, 0), ((0, 0), (0, 0)))

lemma incompatibilityWitness_spec {S : Finset ℕ}
    (hS : ¬ CrossCompatible S S) :
    let w := incompatibilityWitness S
    w.1 ∈ S.product S ∧ w.2.1 ∈ S.product S ∧ w.2.2 ∈ S.product S ∧
    w.1.1 * w.1.2 = w.2.1.1 * w.2.1.2 ∧
    w.1.1 * w.1.2 = w.2.2.1 * w.2.2.2 ∧
    w.1 ≠ w.2.1 ∧ w.1 ≠ w.2.2 ∧ w.2.1 ≠ w.2.2 := by
  classical
  rw [incompatibilityWitness, dif_pos hS]
  exact Classical.choose_spec (exists_incompatibilityCertificate hS)

/-- Indices whose own fiber is not self-compatible. -/
def nonSelfCompatibleIndices (I : Finset ι) (D : ι → Finset ℕ) : Finset ι :=
  I.filter fun i => ¬ CrossCompatible (D i) (D i)

/-- Pairwise-compatible fibers have only polynomially many non-self-compatible
members: their canonical three-representation certificates are distinct. -/
theorem nonSelfCompatibleIndices_card_le
    (I : Finset ι) (D : ι → Finset ℕ) (U : Finset ℕ)
    (hDU : ∀ i ∈ I, D i ⊆ U)
    (hcompat : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      CrossCompatible (D i) (D j)) :
    (nonSelfCompatibleIndices I D).card ≤ U.card ^ 6 := by
  classical
  let Pairs := U.product U
  let Certs := Pairs.product (Pairs.product Pairs)
  have hmap : Set.MapsTo (fun i => incompatibilityWitness (D i))
      (nonSelfCompatibleIndices I D : Set ι) (Certs : Set _) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hs := incompatibilityWitness_spec hi'.2
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨hDU i hi'.1 (Finset.mem_product.mp hs.1).1,
        hDU i hi'.1 (Finset.mem_product.mp hs.1).2⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨hDU i hi'.1 (Finset.mem_product.mp hs.2.1).1,
          hDU i hi'.1 (Finset.mem_product.mp hs.2.1).2⟩
      · apply Finset.mem_product.mpr
        exact ⟨hDU i hi'.1 (Finset.mem_product.mp hs.2.2.1).1,
          hDU i hi'.1 (Finset.mem_product.mp hs.2.2.1).2⟩
  have hinj : Set.InjOn (fun i => incompatibilityWitness (D i))
      (nonSelfCompatibleIndices I D : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    change incompatibilityWitness (D i) = incompatibilityWitness (D j) at hij
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    have hsi := incompatibilityWitness_spec hi'.2
    have hsj := incompatibilityWitness_spec hj'.2
    have hc := hcompat i hi'.1 j hj'.1 hne
    have hw1 : (incompatibilityWitness (D i)).1 ∈ (D j).product (D j) := by
      rw [hij]
      exact hsj.1
    have hw2 : (incompatibilityWitness (D i)).2.1 ∈ (D j).product (D j) := by
      rw [hij]
      exact hsj.2.1
    have hw3 : (incompatibilityWitness (D i)).2.2 ∈ (D j).product (D j) := by
      rw [hij]
      exact hsj.2.2.1
    exact (three_cross_representations_not_compatible
      (S := D i) (T := D j)
      (x₁ := (incompatibilityWitness (D i)).1.1)
      (y₁ := (incompatibilityWitness (D i)).1.2)
      (x₂ := (incompatibilityWitness (D i)).2.1.1)
      (y₂ := (incompatibilityWitness (D i)).2.1.2)
      (x₃ := (incompatibilityWitness (D i)).2.2.1)
      (y₃ := (incompatibilityWitness (D i)).2.2.2)
      (m := (incompatibilityWitness (D i)).1.1 *
        (incompatibilityWitness (D i)).1.2)
      (Finset.mem_product.mp hsi.1).1 (Finset.mem_product.mp hw1).2
      (Finset.mem_product.mp hsi.2.1).1 (Finset.mem_product.mp hw2).2
      (Finset.mem_product.mp hsi.2.2.1).1 (Finset.mem_product.mp hw3).2
      rfl hsi.2.2.2.1.symm hsi.2.2.2.2.1.symm
      hsi.2.2.2.2.2.1 hsi.2.2.2.2.2.2.1 hsi.2.2.2.2.2.2.2) hc
  have hcard := Finset.card_le_card_of_injOn
    (fun i => incompatibilityWitness (D i)) hmap hinj
  calc
    (nonSelfCompatibleIndices I D).card ≤ Certs.card := hcard
    _ = U.card ^ 6 := by
      simp [Certs, Pairs]
      ring

/-- Self-compatible indices available in one capacity class. -/
def availableSelfCompatibleIndices {R : ℕ}
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R) (j : Fin R) :
    Finset ι :=
  I.filter fun i => CrossCompatible (D i) (D i) ∧ cap i = j

/-- A largest-cardinality self-compatible fiber in one class, or empty. -/
noncomputable def maxSelfCompatibleFiber {R : ℕ}
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R) (j : Fin R) :
    Finset ℕ := by
  classical
  exact if h : (availableSelfCompatibleIndices I D cap j).Nonempty then
    D (Classical.choose (Finset.exists_max_image
      (availableSelfCompatibleIndices I D cap j) (fun i => (D i).card) h))
  else ∅

lemma maxSelfCompatibleFiber_spec {R : ℕ}
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R) (j : Fin R)
    (hA : (availableSelfCompatibleIndices I D cap j).Nonempty) :
    ∃ i ∈ availableSelfCompatibleIndices I D cap j,
      D i = maxSelfCompatibleFiber I D cap j ∧
      ∀ l ∈ availableSelfCompatibleIndices I D cap j,
        (D l).card ≤ (maxSelfCompatibleFiber I D cap j).card := by
  classical
  unfold maxSelfCompatibleFiber
  rw [dif_pos hA]
  let i := Classical.choose (Finset.exists_max_image
    (availableSelfCompatibleIndices I D cap j) (fun i => (D i).card) hA)
  have hi := Classical.choose_spec (Finset.exists_max_image
    (availableSelfCompatibleIndices I D cap j) (fun i => (D i).card) hA)
  exact ⟨i, hi.1, rfl, hi.2⟩

lemma maxSelfCompatibleFiber_eq_empty {R : ℕ}
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R) (j : Fin R)
    (hA : ¬(availableSelfCompatibleIndices I D cap j).Nonempty) :
    maxSelfCompatibleFiber I D cap j = ∅ := by
  simp [maxSelfCompatibleFiber, hA]

lemma empty_crossCompatible_left (S : Finset ℕ) :
    CrossCompatible ∅ S := by
  simp [CrossCompatible, crossMultiplicity]

lemma empty_crossCompatible_right (S : Finset ℕ) :
    CrossCompatible S ∅ := by
  simp [CrossCompatible, crossMultiplicity]

/-- All self-compatible fibers, whether repeated or not, are enveloped by a
single compatible profile. -/
theorem exists_polynomialEnvelopeProfile {R : ℕ} (hR : 0 < R)
    (I : Finset ι) (D : ι → Finset ℕ) (cap : ι → Fin R)
    (hpos : ∀ i ∈ I, ∀ d ∈ D i, 0 < d)
    (hbound : ∀ i ∈ I, ∀ d ∈ D i, d ≤ (cap i).val + 1)
    (hcompat : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → CrossCompatible (D i) (D j)) :
    ∃ P : FiberProfile R,
      ∀ i ∈ I, i ∉ nonSelfCompatibleIndices I D →
        (D i).card ≤ (P.fiber (cap i)).card := by
  classical
  let F : Fin R → Finset ℕ := fun j => maxSelfCompatibleFiber I D cap j
  have hFmem : ∀ j : Fin R, F j = ∅ ∨
      CrossCompatible (F j) (F j) ∧
        ∃ i ∈ I, cap i = j ∧ D i = F j := by
    intro j
    by_cases hA : (availableSelfCompatibleIndices I D cap j).Nonempty
    · right
      rcases maxSelfCompatibleFiber_spec I D cap j hA with
        ⟨i, hi, hDi, hmax⟩
      have hi' := Finset.mem_filter.mp hi
      constructor
      · change CrossCompatible (maxSelfCompatibleFiber I D cap j)
          (maxSelfCompatibleFiber I D cap j)
        rw [← hDi]
        exact hi'.2.1
      · refine ⟨i, hi'.1, hi'.2.2, ?_⟩
        change D i = maxSelfCompatibleFiber I D cap j
        exact hDi
    · left
      exact maxSelfCompatibleFiber_eq_empty I D cap j hA
  have hFpos : ∀ j d, d ∈ F j → 0 < d := by
    intro j d hd
    rcases hFmem j with hempty | hmem
    · simp [hempty] at hd
    · rcases hmem.2 with ⟨i, hi, hcap, hDi⟩
      apply hpos i hi d
      rw [hDi]
      exact hd
  have hFbound : ∀ j d, d ∈ F j → d ≤ j.val + 1 := by
    intro j d hd
    rcases hFmem j with hempty | hmem
    · simp [hempty] at hd
    · rcases hmem.2 with ⟨i, hi, hcap, hDi⟩
      have hd' : d ∈ D i := by rw [hDi]; exact hd
      have hb := hbound i hi d hd'
      rw [hcap] at hb
      exact hb
  have hFcompat : ∀ j k, CrossCompatible (F j) (F k) := by
    intro j k
    rcases hFmem j with hj | hj
    · rw [hj]
      exact empty_crossCompatible_left _
    rcases hFmem k with hk | hk
    · rw [hk]
      exact empty_crossCompatible_right _
    rcases hj.2 with ⟨i, hi, hci, hDi⟩
    rcases hk.2 with ⟨l, hl, hcl, hDl⟩
    by_cases hil : i = l
    · subst l
      have hjk : j = k := hci.symm.trans hcl
      subst k
      rw [hci]
      exact hj.1
    · have hc := hcompat i hi l hl hil
      rw [hDi, hDl] at hc
      exact hc
  let P : FiberProfile R :=
    { posR := hR
      fiber := F
      positive := hFpos
      bounded := hFbound
      compatible := hFcompat }
  refine ⟨P, ?_⟩
  intro i hi hgood
  have hself : CrossCompatible (D i) (D i) := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hi, h⟩)
  have hav : i ∈ availableSelfCompatibleIndices I D cap (cap i) :=
    Finset.mem_filter.mpr ⟨hi, hself, rfl⟩
  have hA : (availableSelfCompatibleIndices I D cap (cap i)).Nonempty :=
    ⟨i, hav⟩
  rcases maxSelfCompatibleFiber_spec I D cap (cap i) hA with
    ⟨l, hl, hDl, hmax⟩
  change (D i).card ≤ (F (cap i)).card
  exact hmax i hav

/-- Truncated extracted fibers have the improved envelope with at most `R⁶`
non-self-compatible labels. -/
theorem exists_polynomial_truncatedFiberEnvelope
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ∃ P : FiberProfile R,
      (∀ q ∈ sqrtPrimeLabels n,
        q ∉ nonSelfCompatibleIndices (sqrtPrimeLabels n)
          (fun r => truncatedExtractedFiber A n R r) →
        (truncatedExtractedFiber A n R q).card ≤
          (P.fiber (cutoffCapacityIndex R hR (n / q))).card) ∧
      (nonSelfCompatibleIndices (sqrtPrimeLabels n)
        (fun r => truncatedExtractedFiber A n R r)).card ≤ R ^ 6 := by
  classical
  let I := sqrtPrimeLabels n
  let D : ℕ → Finset ℕ := fun q => truncatedExtractedFiber A n R q
  let cap : ℕ → Fin R := fun q => cutoffCapacityIndex R hR (n / q)
  have hpos : ∀ q ∈ I, ∀ d ∈ D q, 0 < d := by
    intro q hq d hd
    exact (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
  have hbound : ∀ q ∈ I, ∀ d ∈ D q, d ≤ (cap q).val + 1 := by
    intro q hq d hd
    have hd' := Finset.mem_filter.mp hd
    have hdExtract := Finset.mem_filter.mp hd'.1
    have hqdle : q * d ≤ n := (Finset.mem_Icc.mp (hAint hdExtract.2)).2
    have hqprime := (Finset.mem_filter.mp hq).2
    have hdJ : d ≤ n / q := (Nat.le_div_iff_mul_le hqprime.pos).2 (by
      simpa [Nat.mul_comm] using hqdle)
    dsimp [cap, cutoffCapacityIndex]
    omega
  have hcompat : ∀ q ∈ I, ∀ r ∈ I, q ≠ r →
      CrossCompatible (D q) (D r) := by
    intro q hq r hr hqr
    have hq' := Finset.mem_filter.mp hq
    have hr' := Finset.mem_filter.mp hr
    have hbase := extractedFiber_crossCompatible
      (K := n.sqrt) (q := q) (r := r) hA
      (by have := (Finset.mem_Icc.mp hq'.1).1; omega)
      (by have := (Finset.mem_Icc.mp hr'.1).1; omega)
      hq'.2 hr'.2 hqr
    exact hbase.mono
      (fun d hd => (Finset.mem_filter.mp hd).1)
      (fun d hd => (Finset.mem_filter.mp hd).1)
  rcases exists_polynomialEnvelopeProfile hR I D cap hpos hbound hcompat with
    ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  have hDU : ∀ q ∈ I, D q ⊆ Finset.Icc 1 R := by
    intro q hq d hd
    have hd' := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd'.1).1).1, hd'.2⟩
  have hb := nonSelfCompatibleIndices_card_le I D (Finset.Icc 1 R)
    hDU hcompat
  simpa [I, D, hR] using hb

/-- Aggregate truncated-fiber count with polynomial exceptional error. -/
theorem exists_profile_sum_bound_truncatedFibers_polynomial
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ∃ P : FiberProfile R,
      (∑ q ∈ sqrtPrimeLabels n,
        (truncatedExtractedFiber A n R q).card) ≤
      (∑ q ∈ sqrtPrimeLabels n,
        (P.fiber (cutoffCapacityIndex R hR (n / q))).card) + R ^ 7 := by
  classical
  rcases exists_polynomial_truncatedFiberEnvelope hR hAint hA with
    ⟨P, henv, hexc⟩
  let I := sqrtPrimeLabels n
  let D : ℕ → Finset ℕ := fun q => truncatedExtractedFiber A n R q
  let cap : ℕ → Fin R := fun q => cutoffCapacityIndex R hR (n / q)
  let E := nonSelfCompatibleIndices I D
  have hDcard : ∀ q ∈ I, (D q).card ≤ R := by
    intro q hq
    have hsub : D q ⊆ Finset.Icc 1 R := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd'.1).1).1, hd'.2⟩
    simpa [hR] using Finset.card_le_card hsub
  have hpoint : ∀ q ∈ I,
      (D q).card ≤ (P.fiber (cap q)).card + if q ∈ E then R else 0 := by
    intro q hq
    by_cases hqE : q ∈ E
    · rw [if_pos hqE]
      exact (hDcard q hq).trans (Nat.le_add_left _ _)
    · rw [if_neg hqE, Nat.add_zero]
      exact henv q hq hqE
  refine ⟨P, ?_⟩
  change (∑ q ∈ I, (D q).card) ≤
    (∑ q ∈ I, (P.fiber (cap q)).card) + R ^ 7
  calc
    (∑ q ∈ I, (D q).card) ≤
        ∑ q ∈ I, ((P.fiber (cap q)).card + if q ∈ E then R else 0) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ I, (P.fiber (cap q)).card) + R * E.card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter]
      have hf : I.filter (fun q => q ∈ E) = E := by
        ext q
        simp [E, nonSelfCompatibleIndices]
      rw [hf, Finset.sum_const, nsmul_eq_mul]
      simp [Nat.mul_comm]
    _ ≤ (∑ q ∈ I, (P.fiber (cap q)).card) + R ^ 7 := by
      have hm := Nat.mul_le_mul_left R hexc
      rw [show R ^ 7 = R * R ^ 6 by ring]
      exact Nat.add_le_add_left hm _

/-- Uniform truncated-fiber variational bound with the polynomial `R⁷`
exceptional term. -/
theorem truncatedFiberSum_div_le_variational_polynomial
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R) (hn : 1 < n)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ((∑ q ∈ sqrtPrimeLabels n,
      (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) ≤
      primeMass R + variationalLimit + profileApproxError R hR n +
        (R ^ 7 : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) := by
  rcases exists_profile_sum_bound_truncatedFibers_polynomial hR hAint hA with
    ⟨P, hP⟩
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := by
    exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hPR : ((∑ q ∈ sqrtPrimeLabels n,
      (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) ≤
      (P.baseCount n : ℝ) + (R ^ 7 : ℕ) := by
    rw [← profile_sum_eq_baseCount hR P n]
    exact_mod_cast hP
  have hbase := P.baseCount_div_le_beta_add_error hR hn
  have hbeta : P.beta ≤ primeMass R + variationalLimit := by
    have hg := P.gamma_le_variationalLimit
    unfold FiberProfile.gamma at hg
    linarith
  calc
    ((∑ q ∈ sqrtPrimeLabels n,
        (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
      ((P.baseCount n : ℝ) + (R ^ 7 : ℕ)) /
          ((n : ℝ) / Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right hPR hden.le
    _ = (P.baseCount n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) +
        (R ^ 7 : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) := by ring
    _ ≤ _ := by linarith

end PolynomialEnvelope

end Erdos796
