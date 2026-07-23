import Research.SmoothRankin

namespace Erdos796

open Filter Topology

/-- Label/core incidences counted by the extracted tail. -/
def canonicalTailPairs (A : Finset ℕ) (n R : ℕ) : Finset (ℕ × ℕ) :=
  ((sqrtPrimeLabels n).product (Finset.Icc 1 n.sqrt)).filter fun qd =>
    R < qd.2 ∧ qd.1 * qd.2 ∈ A

lemma canonicalTailPairs_card_eq (A : Finset ℕ) (n R : ℕ) :
    (canonicalTailPairs A n R).card = extractedTailSum A n R := by
  unfold canonicalTailPairs extractedTailSum tailExtractedFiber extractedFiber
  rw [Finset.card_filter]
  calc
    (∑ x ∈ (sqrtPrimeLabels n).product (Finset.Icc 1 n.sqrt),
        if R < x.2 ∧ x.1 * x.2 ∈ A then 1 else 0) =
        ∑ q ∈ sqrtPrimeLabels n, ∑ d ∈ Finset.Icc 1 n.sqrt,
          if R < d ∧ q * d ∈ A then 1 else 0 := by
      exact Finset.sum_product _ _ _
    _ = ∑ q ∈ sqrtPrimeLabels n,
        {d ∈ {d ∈ Finset.Icc 1 n.sqrt | q * d ∈ A} | R < d}.card := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hR : R < d <;> by_cases hA : q * d ∈ A <;> simp [hR, hA]

/-- Cofactors occurring at one canonical greatest-prime cell `(q,p)`. -/
noncomputable def canonicalCellCoefficients
    (A : Finset ℕ) (n R q p : ℕ) : Finset ℕ := by
  classical
  exact ((tailExtractedFiber A n R q).filter fun d =>
    greatestPrimeFactor d = p).image greatestPrimeCofactor

/-- Largest cofactor at a canonical cell, with default zero at an empty cell. -/
noncomputable def canonicalCellMax
    (A : Finset ℕ) (n R q p : ℕ) : ℕ :=
  (canonicalCellCoefficients A n R q p).sup id

lemma greatestPrimeCofactor_mem_cell
    {A : Finset ℕ} {n R q d : ℕ} (hd : d ∈ tailExtractedFiber A n R q) :
    greatestPrimeCofactor d ∈ canonicalCellCoefficients A n R q
      (greatestPrimeFactor d) := by
  classical
  unfold canonicalCellCoefficients
  apply Finset.mem_image.mpr
  exact ⟨d, Finset.mem_filter.mpr ⟨hd, rfl⟩, rfl⟩

lemma greatestPrimeCofactor_le_cellMax
    {A : Finset ℕ} {n R q d : ℕ} (hd : d ∈ tailExtractedFiber A n R q) :
    greatestPrimeCofactor d ≤ canonicalCellMax A n R q
      (greatestPrimeFactor d) := by
  classical
  unfold canonicalCellMax
  exact Finset.le_sup (f := id) (greatestPrimeCofactor_mem_cell hd)

lemma canonicalCellMax_pos
    {A : Finset ℕ} {n R q p : ℕ}
    (hcell : (canonicalCellCoefficients A n R q p).Nonempty) :
    0 < canonicalCellMax A n R q p := by
  classical
  rcases hcell with ⟨t, ht⟩
  rcases Finset.mem_image.mp ht with ⟨d, hd, rfl⟩
  have htail := (Finset.mem_filter.mp hd).1
  have hdI := Finset.mem_filter.mp htail
  have hdpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdI.1).1).1
  have htpos : 0 < greatestPrimeCofactor d := by
    by_cases hdgt : 1 < d
    · exact greatestPrimeCofactor_pos hdgt
    · have hd1 : d = 1 := by omega
      subst d
      simp [greatestPrimeCofactor, greatestPrimeFactor]
  exact lt_of_lt_of_le htpos (Finset.le_sup (f := id) ht)

/-- Coefficients through a dyadic endpoint which are smooth at the dyadic
prime endpoint. -/
def canonicalCoefficientRange (j k : ℕ) : Finset ℕ :=
  Nat.smoothNumbersUpTo (2 ^ (j + 1)) (2 ^ (k + 1))

/-- Large-prime labels in one dyadic interval. -/
def canonicalLabelRange (n i : ℕ) : Finset ℕ :=
  dyadicPrimes i ∩ sqrtPrimeLabels n

/-- One cell-maximal canonical dyadic block. All incidences sharing a cell
belong to the same block, a feature which prevents repeated baseline charges. -/
noncomputable def canonicalDyadicBlock
    (A : Finset ℕ) (n R i j k : ℕ) :
    Finset (↥(canonicalCoefficientRange j k) ×
      (↥(canonicalLabelRange n i) × ↥(dyadicPrimes k))) := by
  classical
  exact Finset.univ.filter fun e =>
    let t := (e.1 : ℕ)
    let q := (e.2.1 : ℕ)
    let p := (e.2.2 : ℕ)
    t * p ∈ tailExtractedFiber A n R q ∧
      greatestPrimeFactor (t * p) = p ∧
      Nat.log2 (canonicalCellMax A n R q p) = j

/-- The active `(q,p)` cells of one canonical dyadic block. -/
noncomputable def canonicalDyadicActiveCells
    (A : Finset ℕ) (n R i j k : ℕ) :
    Finset (↥(canonicalLabelRange n i) × ↥(dyadicPrimes k)) :=
  activeCells (canonicalDyadicBlock A n R i j k)

lemma cofactor_mem_canonicalCoefficientRange
    {A : Finset ℕ} {n R q d i j k : ℕ}
    (hRpos : 0 < R)
    (hd : d ∈ tailExtractedFiber A n R q)
    (hqi : q ∈ dyadicPrimes i)
    (hpk : greatestPrimeFactor d ∈ dyadicPrimes k)
    (hj : Nat.log2 (canonicalCellMax A n R q
      (greatestPrimeFactor d)) = j) :
    greatestPrimeCofactor d ∈ canonicalCoefficientRange j k := by
  have hdTail := Finset.mem_filter.mp hd
  have hdI := Finset.mem_filter.mp hdTail.1
  have hdgt : 1 < d := by
    have hdpos := (Finset.mem_Icc.mp hdI.1).1
    omega
  have htpos := greatestPrimeCofactor_pos hdgt
  have htMax := greatestPrimeCofactor_le_cellMax hd
  have hmaxpos : canonicalCellMax A n R q (greatestPrimeFactor d) ≠ 0 := by
    omega
  have hmaxdy := mem_dyadicInterval_log2 hmaxpos
  rw [hj] at hmaxdy
  have htBound : greatestPrimeCofactor d ≤ 2 ^ (j + 1) :=
    htMax.trans (Finset.mem_Ico.mp hmaxdy).2.le
  rw [canonicalCoefficientRange, Nat.mem_smoothNumbersUpTo]
  constructor
  · exact htBound
  · constructor
    · exact Nat.ne_of_gt htpos
    · intro r hrlist
      have hrdesc := (Nat.mem_primeFactorsList (Nat.ne_of_gt htpos)).mp hrlist
      have hrdivd : r ∣ d := by
        rw [← greatestPrimeCofactor_mul_factor hdgt]
        exact dvd_mul_of_dvd_left hrdesc.2 _
      have hrle := prime_dvd_le_greatestPrimeFactor hdgt hrdesc.1 hrdivd
      have hpUpper := (Finset.mem_Ico.mp (Finset.mem_filter.mp hpk).1).2
      omega

/-- Tail pairs assigned to one dyadic label/max-coefficient/prime block. -/
noncomputable def canonicalTailPairBlock
    (A : Finset ℕ) (n R i j k : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (canonicalTailPairs A n R).filter fun qd =>
    Nat.log2 qd.1 = i ∧
      Nat.log2 (canonicalCellMax A n R qd.1
        (greatestPrimeFactor qd.2)) = j ∧
      Nat.log2 (greatestPrimeFactor qd.2) = k

/-- Every tail pair has its canonical dyadic encoding in the corresponding
cell-max block. -/
lemma tailPair_mem_canonicalDyadicBlock
    {A : Finset ℕ} {n R q d : ℕ} (hRpos : 0 < R)
    (hpair : (q, d) ∈ canonicalTailPairs A n R) :
    let i := Nat.log2 q
    let j := Nat.log2 (canonicalCellMax A n R q (greatestPrimeFactor d))
    let k := Nat.log2 (greatestPrimeFactor d)
    (⟨greatestPrimeCofactor d,
        cofactor_mem_canonicalCoefficientRange hRpos
          (by
            unfold tailExtractedFiber extractedFiber
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2,
                (Finset.mem_filter.mp hpair).2.2⟩,
              (Finset.mem_filter.mp hpair).2.1⟩)
          (by
            exact Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2
              (by
                have hq := Finset.mem_product.mp (Finset.mem_filter.mp hpair).1
                exact (Finset.mem_filter.mp hq.1).2.ne_zero),
              (Finset.mem_filter.mp
                (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1).2⟩)
          (by
            have hdTail : d ∈ tailExtractedFiber A n R q := by
              unfold tailExtractedFiber extractedFiber
              exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2,
                  (Finset.mem_filter.mp hpair).2.2⟩,
                (Finset.mem_filter.mp hpair).2.1⟩
            have hdgt : 1 < d := by
              have hdpos := (Finset.mem_Icc.mp
                (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2).1
              have htail := (Finset.mem_filter.mp hpair).2.1
              omega
            exact Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2
              (greatestPrimeFactor_prime hdgt).ne_zero,
              greatestPrimeFactor_prime hdgt⟩)
          rfl⟩,
      (⟨q, by
          have hq := Finset.mem_product.mp (Finset.mem_filter.mp hpair).1
          apply Finset.mem_inter.mpr
          exact ⟨Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2
            (Finset.mem_filter.mp hq.1).2.ne_zero,
            (Finset.mem_filter.mp hq.1).2⟩, hq.1⟩⟩,
       ⟨greatestPrimeFactor d, by
          have hdpos := (Finset.mem_Icc.mp
            (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2).1
          have htail := (Finset.mem_filter.mp hpair).2.1
          have hdgt : 1 < d := by omega
          exact Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2
            (greatestPrimeFactor_prime hdgt).ne_zero,
            greatestPrimeFactor_prime hdgt⟩⟩)) ∈
      canonicalDyadicBlock A n R i j k := by
  dsimp
  classical
  rw [canonicalDyadicBlock, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have hp := Finset.mem_filter.mp hpair
  have hqD := Finset.mem_product.mp hp.1
  have hdgt : 1 < d := by
    have hdpos := (Finset.mem_Icc.mp hqD.2).1
    omega
  have hdTail : d ∈ tailExtractedFiber A n R q := by
    unfold tailExtractedFiber extractedFiber
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqD.2, hp.2.2⟩, hp.2.1⟩
  rw [greatestPrimeCofactor_mul_factor hdgt]
  simpa using hdTail

lemma canonicalCellMax_le_sqrt
    {A : Finset ℕ} {n R q p : ℕ} :
    canonicalCellMax A n R q p ≤ n.sqrt := by
  classical
  unfold canonicalCellMax
  apply Finset.sup_le
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨d, hd, rfl⟩
  have hd' := Finset.mem_filter.mp hd
  have htail := Finset.mem_filter.mp hd'.1
  have hfiber := Finset.mem_filter.mp htail.1
  have hdpos := (Finset.mem_Icc.mp hfiber.1).1
  by_cases hdgt : 1 < d
  · have hpPos := (greatestPrimeFactor_prime hdgt).pos
    have hprod := greatestPrimeCofactor_mul_factor hdgt
    calc
      greatestPrimeCofactor d ≤
          greatestPrimeCofactor d * greatestPrimeFactor d :=
        Nat.le_mul_of_pos_right _ hpPos
      _ = d := hprod
      _ ≤ n.sqrt := (Finset.mem_Icc.mp hfiber.1).2
  · have hd1 : d = 1 := by omega
    subst d
    simpa [greatestPrimeCofactor, greatestPrimeFactor] using
      (Finset.mem_Icc.mp hfiber.1).2

/-- Every tail pair lies in one of the dyadic blocks indexed through
`log₂ n`. -/
theorem canonicalTailPairs_subset_dyadicBlocks
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R) :
    canonicalTailPairs A n R ⊆
      (dyadicIndexCube n).biUnion fun e =>
        canonicalTailPairBlock A n R e.1 e.2.1 e.2.2 := by
  classical
  intro qd hqd
  have hp := Finset.mem_filter.mp hqd
  have hprod := Finset.mem_product.mp hp.1
  have hqLabel := Finset.mem_filter.mp hprod.1
  have hdI := Finset.mem_Icc.mp hprod.2
  have hdgt : 1 < qd.2 := by omega
  let p := greatestPrimeFactor qd.2
  let m := canonicalCellMax A n R qd.1 p
  have hpPos : 0 < p := greatestPrimeFactor_prime hdgt |>.pos
  have hpDvd := greatestPrimeFactor_dvd hdgt
  have hpLeD : p ≤ qd.2 := Nat.le_of_dvd (by omega) hpDvd
  have hqLe : qd.1 ≤ n := (Finset.mem_Icc.mp hqLabel.1).2
  have hpLe : p ≤ n := hpLeD.trans (hdI.2.trans (Nat.sqrt_le_self n))
  have hmLe : m ≤ n := canonicalCellMax_le_sqrt.trans (Nat.sqrt_le_self n)
  have htail : qd.2 ∈ tailExtractedFiber A n R qd.1 := by
    unfold tailExtractedFiber extractedFiber
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hprod.2, hp.2.2⟩, hp.2.1⟩
  have hmPos : 0 < m := by
    unfold m
    apply canonicalCellMax_pos
    exact ⟨greatestPrimeCofactor qd.2,
      greatestPrimeCofactor_mem_cell htail⟩
  have hi : Nat.log2 qd.1 ≤ Nat.log2 n :=
    log2_mono_of_le hqLabel.2.ne_zero hqLe
  have hj : Nat.log2 m ≤ Nat.log2 n :=
    log2_mono_of_le (Nat.ne_of_gt hmPos) hmLe
  have hk : Nat.log2 p ≤ Nat.log2 n :=
    log2_mono_of_le (Nat.ne_of_gt hpPos) hpLe
  let e : ℕ × (ℕ × ℕ) :=
    (Nat.log2 qd.1, (Nat.log2 m, Nat.log2 p))
  apply Finset.mem_biUnion.mpr
  refine ⟨e, ?_, ?_⟩
  · unfold dyadicIndexCube
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi),
       Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj),
         Finset.mem_range.mpr (Nat.lt_succ_of_le hk)⟩⟩
  · unfold canonicalTailPairBlock
    apply Finset.mem_filter.mpr
    exact ⟨hqd, rfl, rfl, rfl⟩

/-- Canonical greatest-prime encoding is a bijection on every tail-pair
block. -/
theorem canonicalTailPairBlock_card_eq
    {A : Finset ℕ} {n R i j k : ℕ} (hR : 0 < R) :
    (canonicalTailPairBlock A n R i j k).card =
      (canonicalDyadicBlock A n R i j k).card := by
  classical
  let S := canonicalTailPairBlock A n R i j k
  let H := canonicalDyadicBlock A n R i j k
  let enc : (qd : ℕ × ℕ) → qd ∈ S →
      ↥(canonicalCoefficientRange j k) ×
        (↥(canonicalLabelRange n i) × ↥(dyadicPrimes k)) := fun qd hqd => by
    have hb := (Finset.mem_filter.mp hqd).2
    have hpair := (Finset.mem_filter.mp hqd).1
    refine (⟨greatestPrimeCofactor qd.2, ?_⟩,
      (⟨qd.1, ?_⟩, ⟨greatestPrimeFactor qd.2, ?_⟩))
    · exact cofactor_mem_canonicalCoefficientRange (i := i) (j := j) (k := k) hR
        (by
          unfold tailExtractedFiber extractedFiber
          have hp := Finset.mem_filter.mp hpair
          have hprod := Finset.mem_product.mp hp.1
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨hprod.2, hp.2.2⟩, hp.2.1⟩)
        (by
          have hp := Finset.mem_filter.mp hpair
          have hq := Finset.mem_product.mp hp.1
          rw [← hb.1]
          exact Finset.mem_filter.mpr
            ⟨mem_dyadicInterval_log2
              (Finset.mem_filter.mp hq.1).2.ne_zero,
             (Finset.mem_filter.mp hq.1).2⟩)
        (by
          have hp := Finset.mem_filter.mp hpair
          have hprod := Finset.mem_product.mp hp.1
          have hdgt : 1 < qd.2 := by
            have hdpos := (Finset.mem_Icc.mp hprod.2).1
            omega
          rw [← hb.2.2]
          exact Finset.mem_filter.mpr
            ⟨mem_dyadicInterval_log2
              (greatestPrimeFactor_prime hdgt).ne_zero,
             greatestPrimeFactor_prime hdgt⟩)
        hb.2.1
    · apply Finset.mem_inter.mpr
      have hp := Finset.mem_filter.mp hpair
      have hq := Finset.mem_product.mp hp.1
      exact ⟨by
        rw [← hb.1]
        exact Finset.mem_filter.mpr
          ⟨mem_dyadicInterval_log2
            (Finset.mem_filter.mp hq.1).2.ne_zero,
           (Finset.mem_filter.mp hq.1).2⟩, hq.1⟩
    · have hp := Finset.mem_filter.mp hpair
      have hprod := Finset.mem_product.mp hp.1
      have hdgt : 1 < qd.2 := by
        have hdpos := (Finset.mem_Icc.mp hprod.2).1
        omega
      rw [← hb.2.2]
      exact Finset.mem_filter.mpr
        ⟨mem_dyadicInterval_log2
          (greatestPrimeFactor_prime hdgt).ne_zero,
         greatestPrimeFactor_prime hdgt⟩
  let dec : (e : ↥(canonicalCoefficientRange j k) ×
        (↥(canonicalLabelRange n i) × ↥(dyadicPrimes k))) → e ∈ H →
      ℕ × ℕ := fun e _ => ((e.2.1 : ℕ), (e.1 : ℕ) * (e.2.2 : ℕ))
  refine Finset.card_bij' enc dec ?_ ?_ ?_ ?_
  · intro qd hqd
    have hb := (Finset.mem_filter.mp hqd).2
    have hpair := (Finset.mem_filter.mp hqd).1
    have hp := Finset.mem_filter.mp hpair
    have hprod := Finset.mem_product.mp hp.1
    have hdgt : 1 < qd.2 := by
      have hdpos := (Finset.mem_Icc.mp hprod.2).1
      omega
    change enc qd hqd ∈ canonicalDyadicBlock A n R i j k
    rw [canonicalDyadicBlock, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change greatestPrimeCofactor qd.2 * greatestPrimeFactor qd.2 ∈
        tailExtractedFiber A n R qd.1 ∧
      greatestPrimeFactor
          (greatestPrimeCofactor qd.2 * greatestPrimeFactor qd.2) =
        greatestPrimeFactor qd.2 ∧
      Nat.log2 (canonicalCellMax A n R qd.1
        (greatestPrimeFactor qd.2)) = j
    rw [greatestPrimeCofactor_mul_factor hdgt]
    exact ⟨by
      unfold tailExtractedFiber extractedFiber
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨hprod.2, hp.2.2⟩, hp.2.1⟩, rfl, hb.2.1⟩
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    change ((e.2.1 : ℕ), (e.1 : ℕ) * (e.2.2 : ℕ)) ∈
      canonicalTailPairBlock A n R i j k
    unfold canonicalTailPairBlock
    apply Finset.mem_filter.mpr
    constructor
    · unfold canonicalTailPairs
      apply Finset.mem_filter.mpr
      have htail := Finset.mem_filter.mp he'.1
      have hfiber := Finset.mem_filter.mp htail.1
      have hqrange := Finset.mem_inter.mp e.2.1.2
      exact ⟨Finset.mem_product.mpr ⟨hqrange.2, hfiber.1⟩,
        htail.2, hfiber.2⟩
    · have hqdy := Finset.mem_filter.mp (Finset.mem_inter.mp e.2.1.2).1
      have hpdy := Finset.mem_filter.mp e.2.2.2
      exact ⟨by
        have hq0 := hqdy.2.ne_zero
        exact (Nat.log2_eq_iff hq0).2 (Finset.mem_Ico.mp hqdy.1),
        by simpa [he'.2.1] using he'.2.2, by
          have hp0 := hpdy.2.ne_zero
          rw [he'.2.1]
          exact (Nat.log2_eq_iff hp0).2 (Finset.mem_Ico.mp hpdy.1)⟩
  · intro qd hqd
    have hpair := (Finset.mem_filter.mp hqd).1
    have hp := Finset.mem_filter.mp hpair
    have hprod := Finset.mem_product.mp hp.1
    have hdgt : 1 < qd.2 := by
      have hdpos := (Finset.mem_Icc.mp hprod.2).1
      omega
    change (qd.1, greatestPrimeCofactor qd.2 *
      greatestPrimeFactor qd.2) = qd
    apply Prod.ext
    · rfl
    · exact greatestPrimeCofactor_mul_factor hdgt
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    apply Prod.ext
    · apply Subtype.ext
      have hdgt : 1 < (e.1 : ℕ) * (e.2.2 : ℕ) := by
        have ht := Finset.mem_filter.mp he'.1
        omega
      have hprod := greatestPrimeCofactor_mul_factor hdgt
      rw [he'.2.1] at hprod
      exact Nat.eq_of_mul_eq_mul_right
        (Finset.mem_filter.mp e.2.2.2).2.pos hprod
    · apply Prod.ext
      · rfl
      · exact Subtype.ext he'.2.1

/-- The extracted tail is covered by the sum of its canonical dyadic blocks. -/
theorem extractedTailSum_le_canonicalDyadicSum
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R) :
    extractedTailSum A n R ≤
      ∑ e ∈ dyadicIndexCube n,
        (canonicalDyadicBlock A n R e.1 e.2.1 e.2.2).card := by
  classical
  let U := (dyadicIndexCube n).biUnion fun e =>
    canonicalTailPairBlock A n R e.1 e.2.1 e.2.2
  have hsub : canonicalTailPairs A n R ⊆ U :=
    canonicalTailPairs_subset_dyadicBlocks hR
  calc
    extractedTailSum A n R = (canonicalTailPairs A n R).card :=
      (canonicalTailPairs_card_eq A n R).symm
    _ ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ dyadicIndexCube n,
        (canonicalTailPairBlock A n R e.1 e.2.1 e.2.2).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      exact canonicalTailPairBlock_card_eq hR

/-- Every canonical dyadic block is cube-free. -/
theorem canonicalDyadicBlock_cubeFree
    {A : Finset ℕ} {n R i j k : ℕ} (hA : HasRepBound 3 A) :
    CubeFree (canonicalDyadicBlock A n R i j k) := by
  classical
  let D : ↥(canonicalLabelRange n i) → Finset ℕ := fun q =>
    extractedFiber A n.sqrt q.1
  apply canonicalIncidence_cubeFree D
    (fun t : ↥(canonicalCoefficientRange j k) => t.1)
    (fun p : ↥(dyadicPrimes k) => p.1)
  · intro q r hqr
    have hqRange := Finset.mem_inter.mp q.2
    have hrRange := Finset.mem_inter.mp r.2
    have hqLabel := Finset.mem_filter.mp hqRange.2
    have hrLabel := Finset.mem_filter.mp hrRange.2
    apply extractedFiber_crossCompatible hA
      (Finset.mem_Icc.mp hqLabel.1 |>.1 |> fun h => by omega)
      (Finset.mem_Icc.mp hrLabel.1 |>.1 |> fun h => by omega)
      hqLabel.2 hrLabel.2
    intro hval
    apply hqr
    exact Subtype.ext hval
  · intro t q p he
    have he' := Finset.mem_filter.mp he
    exact (Finset.mem_filter.mp he'.2.1).1
  · intro q t u p v htp huv heq
    have htp' := (Finset.mem_filter.mp htp).2
    have huv' := (Finset.mem_filter.mp huv).2
    have hpvNat : (p : ℕ) = (v : ℕ) := by
      rw [← htp'.2.1, ← huv'.2.1, heq]
    have hpv : p = v := Subtype.ext hpvNat
    subst v
    have hpPos : 0 < (p : ℕ) := (Finset.mem_filter.mp p.2).2.pos
    have htuNat : (t : ℕ) = (u : ℕ) :=
      Nat.eq_of_mul_eq_mul_right hpPos (by simpa using heq)
    exact Prod.ext (Subtype.ext htuNat) rfl

lemma canonicalLabelRange_card_le (n i : ℕ) :
    (canonicalLabelRange n i).card ≤ (dyadicPrimes i).card := by
  exact Finset.card_le_card Finset.inter_subset_left

lemma canonicalDyadicActiveCells_card_le (A : Finset ℕ) (n R i j k : ℕ) :
    (canonicalDyadicActiveCells A n R i j k).card ≤
      (canonicalLabelRange n i).card * (dyadicPrimes k).card := by
  unfold canonicalDyadicActiveCells activeCells
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- If a canonical block is occupied, the three dyadic lower endpoints obey
its ambient hyperbolic product constraint. -/
lemma canonicalDyadicBlock_nonempty_product_le
    {A : Finset ℕ} {n R i j k : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n)
    (hne : (canonicalDyadicBlock A n R i j k).Nonempty) :
    2 ^ i * 2 ^ j * 2 ^ k ≤ n := by
  classical
  rcases hne with ⟨e, he⟩
  have he' := (Finset.mem_filter.mp he).2
  let t := (e.1 : ℕ)
  let q := (e.2.1 : ℕ)
  let p := (e.2.2 : ℕ)
  have htail : t * p ∈ tailExtractedFiber A n R q := he'.1
  have hcellMem : t ∈ canonicalCellCoefficients A n R q p := by
    unfold canonicalCellCoefficients
    apply Finset.mem_image.mpr
    exact ⟨t * p, Finset.mem_filter.mpr ⟨htail, he'.2.1⟩, by
      have hdgt : 1 < t * p := by
        have htail' := Finset.mem_filter.mp htail
        omega
      have hprod := greatestPrimeCofactor_mul_factor hdgt
      rw [he'.2.1] at hprod
      exact Nat.eq_of_mul_eq_mul_right
        (Finset.mem_filter.mp e.2.2.2).2.pos hprod⟩
  have hcellNon : (canonicalCellCoefficients A n R q p).Nonempty :=
    ⟨t, hcellMem⟩
  obtain ⟨u, hu, hmaxu⟩ := Finset.exists_mem_eq_sup
    (canonicalCellCoefficients A n R q p) hcellNon id
  have humem := Finset.mem_image.mp hu
  rcases humem with ⟨d, hd, hdu⟩
  have hdFilter := Finset.mem_filter.mp hd
  have hdTail := Finset.mem_filter.mp hdFilter.1
  have hdFiber := Finset.mem_filter.mp hdTail.1
  have hdgt : 1 < d := by omega
  have hqdle : q * d ≤ n := (Finset.mem_Icc.mp (hAint hdFiber.2)).2
  have hdup : u * p = d := by
    rw [← hdu, hdFilter.2.symm]
    exact greatestPrimeCofactor_mul_factor hdgt
  have hqLower : 2 ^ i ≤ q :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp
      (Finset.mem_inter.mp e.2.1.2).1).1).1
  have hpLower : 2 ^ k ≤ p :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp e.2.2.2).1).1
  have hmax : canonicalCellMax A n R q p = u := by
    exact hmaxu.trans rfl
  have hmaxpos : canonicalCellMax A n R q p ≠ 0 := by
    exact Nat.ne_of_gt (canonicalCellMax_pos hcellNon)
  have hjmem := mem_dyadicInterval_log2 hmaxpos
  rw [he'.2.2, hmax] at hjmem
  have huLower : 2 ^ j ≤ u := (Finset.mem_Ico.mp hjmem).1
  calc
    2 ^ i * 2 ^ j * 2 ^ k ≤ q * u * p := by gcongr
    _ = q * (u * p) := by ring
    _ = q * d := by rw [hdup]
    _ ≤ n := hqdle

/-- At the dyadic core cutoff `2^(K+2)`, every occupied tail block has
total coefficient/prime degree strictly above `K`. -/
lemma canonicalDyadicBlock_nonempty_degree_gt
    {A : Finset ℕ} {n K i j k : ℕ}
    (hne : (canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty) :
    K < j + k := by
  rcases hne with ⟨e, he⟩
  have he' := (Finset.mem_filter.mp he).2
  let t := (e.1 : ℕ)
  let p := (e.2.2 : ℕ)
  let q := (e.2.1 : ℕ)
  have htail := Finset.mem_filter.mp he'.1
  have hdgt : 2 ^ (K + 2) < t * p := htail.2
  have htMax : t ≤ canonicalCellMax A n (2 ^ (K + 2)) q p := by
    have hbase := greatestPrimeCofactor_le_cellMax he'.1
    change greatestPrimeCofactor (t * p) ≤
      canonicalCellMax A n (2 ^ (K + 2)) q
        (greatestPrimeFactor (t * p)) at hbase
    have hpow : 1 < 2 ^ (K + 2) := one_lt_pow₀ (by omega) (by norm_num)
    have hcore : 1 < t * p := hpow.trans hdgt
    have hprod := greatestPrimeCofactor_mul_factor hcore
    change greatestPrimeCofactor (t * p) * greatestPrimeFactor (t * p) =
      t * p at hprod
    rw [he'.2.1] at hprod hbase
    have hcof : greatestPrimeCofactor (t * p) = t :=
      Nat.eq_of_mul_eq_mul_right
        (Finset.mem_filter.mp e.2.2.2).2.pos hprod
    rw [hcof] at hbase
    exact hbase
  have hmaxpos : canonicalCellMax A n (2 ^ (K + 2)) q p ≠ 0 := by
    have htpos : 0 < t := (Nat.mem_smoothNumbersUpTo.mp e.1.2).2.1 |> Nat.pos_of_ne_zero
    omega
  have hmaxdy := mem_dyadicInterval_log2 hmaxpos
  rw [he'.2.2] at hmaxdy
  have htUpper : t < 2 ^ (j + 1) :=
    htMax.trans_lt (Finset.mem_Ico.mp hmaxdy).2
  have hpUpper : p < 2 ^ (k + 1) :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp e.2.2.2).1).2
  have hprodUpper : t * p < 2 ^ (j + k + 2) := by
    calc
      t * p < 2 ^ (j + 1) * p :=
        Nat.mul_lt_mul_of_pos_right htUpper
          (Finset.mem_filter.mp e.2.2.2).2.pos
      _ < 2 ^ (j + 1) * 2 ^ (k + 1) :=
        Nat.mul_lt_mul_of_pos_left hpUpper (by positivity)
      _ = 2 ^ (j + k + 2) := by rw [← pow_add]; congr 1 <;> omega
  have hpows : 2 ^ (K + 2) < 2 ^ (j + k + 2) := hdgt.trans hprodUpper
  have hexp : K + 2 < j + k + 2 :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < (2 : ℕ))).mp hpows
  omega

/-- Occupied large-label blocks have dyadic label index at least half the
ambient binary logarithm, up to the harmless endpoint shift. -/
lemma canonicalDyadicBlock_nonempty_log2_lt_two_mul
    {A : Finset ℕ} {n R i j k : ℕ}
    (hne : (canonicalDyadicBlock A n R i j k).Nonempty) :
    Nat.log2 n < 2 * (i + 1) := by
  rcases hne with ⟨e, he⟩
  have hqRange := Finset.mem_inter.mp e.2.1.2
  have hqDy := Finset.mem_filter.mp hqRange.1
  have hqLabel := Finset.mem_filter.mp hqRange.2
  have hqUpper : (e.2.1 : ℕ) < 2 ^ (i + 1) :=
    (Finset.mem_Ico.mp hqDy.1).2
  have hsqrtq : n.sqrt < (e.2.1 : ℕ) := by
    have hI := Finset.mem_Icc.mp hqLabel.1
    omega
  have hnq : n < (e.2.1 : ℕ) * (e.2.1 : ℕ) := Nat.sqrt_lt.mp hsqrtq
  have hnPow : n < 2 ^ (2 * (i + 1)) := by
    rw [show 2 * (i + 1) = (i + 1) + (i + 1) by omega, pow_add]
    exact hnq.trans_le (Nat.mul_le_mul hqUpper.le hqUpper.le)
  by_cases hn0 : n = 0
  · subst n
    simp
  · exact (Nat.log2_lt hn0).2 hnPow

/-- Projection-sensitive estimate for a canonical dyadic block. -/
theorem canonicalDyadicBlock_card_le_active_sqrt
    {A : Finset ℕ} {n R i j k : ℕ} (hA : HasRepBound 3 A) :
    ((canonicalDyadicBlock A n R i j k).card : ℝ) ≤
      (canonicalDyadicActiveCells A n R i j k).card +
      ((canonicalCoefficientRange j k).card : ℝ) *
        Real.sqrt (((canonicalDyadicActiveCells A n R i j k).card : ℝ) *
          (((canonicalLabelRange n i).card : ℝ) +
            (dyadicPrimes k).card *
              Real.sqrt ((canonicalLabelRange n i).card : ℝ))) := by
  have h := cubeFree_card_le_active
    (canonicalDyadicBlock A n R i j k)
    (canonicalDyadicBlock_cubeFree hA)
  simpa [canonicalDyadicActiveCells, activeCells, activeBetaGamma,
    coefficientFiber, alphaFiber, Real.sqrt_mul (by positivity :
      (0 : ℝ) ≤ (canonicalDyadicActiveCells A n R i j k).card)] using h

end Erdos796
