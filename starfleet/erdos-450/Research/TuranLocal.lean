import Research.TuranScores

namespace Erdos450

noncomputable def lowScoreSet (S : Finset ℕ) (s : Finset ℕ) : Finset ℕ := by
  classical
  exact s.filter fun m =>
    (primeScore S m : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S

noncomputable def highSquareScoreSet (S : Finset ℕ) (s : Finset ℕ) : Finset ℕ := by
  classical
  exact s.filter fun m =>
    (3 / 2 : ℝ) * primeReciprocalMean S ≤ (primeSquareScore S m : ℝ)

noncomputable def lowMediumDivisors (S : Finset ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioo n (2 * n)).filter fun d =>
    (primeScore S d : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S

noncomputable def lowDivisorCovered (S : Finset ℕ) (n x y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico x (x + y)).filter fun m =>
    ∃ d ∈ lowMediumDivisors S n, d ∣ m

noncomputable def lowQuotientCovered (S : Finset ℕ) (n x y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico x (x + y)).filter fun m =>
    ∃ d ∈ Finset.Ioo n (2 * n),
      d ∣ m ∧
      ¬(primeScore S d : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S ∧
      (primeScore S (m / d) : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S

/-- Every bad point falls into the low-divisor class, the low-quotient class,
or the high two-level-score class. -/
theorem bad_filter_subset_turan_three_classes
    (S : Finset ℕ) (n x y : ℕ) :
    badFilter n (Finset.Ico x (x + y)) ⊆
      lowDivisorCovered S n x y ∪ lowQuotientCovered S n x y ∪
        highSquareScoreSet S (Finset.Ico x (x + y)) := by
  classical
  intro m hm
  unfold badFilter at hm
  have hm' := Finset.mem_filter.mp hm
  obtain ⟨d, hnd, hd2, hdm⟩ := hm'.2
  by_cases hdlow : (primeScore S d : ℝ) ≤
      (3 / 4 : ℝ) * primeReciprocalMean S
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hm'.1, d, ?_, hdm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hnd, hd2⟩, hdlow⟩
  · by_cases hqlow : (primeScore S (m / d) : ℝ) ≤
        (3 / 4 : ℝ) * primeReciprocalMean S
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      have hmem : m ∈ Finset.Ico x (x + y) ∧
          ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m ∧
            ¬(primeScore S d : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S ∧
            (primeScore S (m / d) : ℝ) ≤
              (3 / 4 : ℝ) * primeReciprocalMean S :=
        ⟨hm'.1, d, Finset.mem_Ioo.mpr ⟨hnd, hd2⟩, hdm, hdlow, hqlow⟩
      simpa only [lowQuotientCovered, Finset.mem_filter] using hmem
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hm'.1, ?_⟩
      have hprod := primeScore_product_le_squareScore S d (m / d)
      have heq : d * (m / d) = m := Nat.mul_div_cancel' hdm
      rw [heq] at hprod
      have hprodR : (primeScore S d : ℝ) + primeScore S (m / d) ≤
          primeSquareScore S m := by exact_mod_cast hprod
      have hdhigh : (3 / 4 : ℝ) * primeReciprocalMean S < primeScore S d :=
        lt_of_not_ge hdlow
      have hqhigh : (3 / 4 : ℝ) * primeReciprocalMean S < primeScore S (m / d) :=
        lt_of_not_ge hqlow
      nlinarith [hprodR]

/-- There are few low-score medium divisors, with the same one-period boundary loss. -/
theorem lowMediumDivisors_weighted_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) (n : ℕ) :
    (lowMediumDivisors S n).card * primeReciprocalMean S ≤
      16 * (n + primeSquarePeriod S) := by
  classical
  have hsub : lowMediumDivisors S n ⊆
      lowScoreSet S (Finset.Ico n (n + n)) := by
    intro d hd
    have hd' : d ∈ Finset.Ioo n (2 * n) ∧
        (primeScore S d : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S := by
      simpa only [lowMediumDivisors, Finset.mem_filter] using hd
    have hdi := Finset.mem_Ioo.mp hd'.1
    have hi : d ∈ Finset.Ico n (n + n) := by
      exact Finset.mem_Ico.mpr ⟨Nat.le_of_lt hdi.1, by omega⟩
    simpa only [lowScoreSet, Finset.mem_filter] using And.intro hi hd'.2
  have hcard : (lowMediumDivisors S n).card ≤
      (lowScoreSet S (Finset.Ico n (n + n))).card :=
    Finset.card_le_card hsub
  have hinterval := low_primeScore_interval_bound S hprime hmu n n
  have hcardR : ((lowMediumDivisors S n).card : ℝ) ≤
      (lowScoreSet S (Finset.Ico n (n + n))).card := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardR hmu.le
  simpa only [lowScoreSet] using le_trans hmul hinterval

/-- Crude union bound for points covered by a low-score medium divisor. -/
theorem lowDivisorCovered_card_le (S : Finset ℕ) (n x y : ℕ) (hn : 0 < n) :
    (lowDivisorCovered S n x y).card ≤
      (lowMediumDivisors S n).card * (y / n + 1) := by
  classical
  let U : ℕ → Finset ℕ := fun d =>
    (Finset.Ico x (x + y)).filter (fun m => d ∣ m)
  have hsub : lowDivisorCovered S n x y ⊆
      (lowMediumDivisors S n).biUnion U := by
    intro m hm
    have hm' : m ∈ Finset.Ico x (x + y) ∧
        ∃ d ∈ lowMediumDivisors S n, d ∣ m := by
      simpa only [lowDivisorCovered, Finset.mem_filter] using hm
    obtain ⟨d, hd, hdm⟩ := hm'.2
    exact Finset.mem_biUnion.mpr
      ⟨d, hd, Finset.mem_filter.mpr ⟨hm'.1, hdm⟩⟩
  calc
    (lowDivisorCovered S n x y).card
        ≤ ((lowMediumDivisors S n).biUnion U).card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ lowMediumDivisors S n, (U d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ lowMediumDivisors S n, (y / n + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdf : d ∈ (Finset.Ioo n (2 * n)).filter (fun d =>
          (primeScore S d : ℝ) ≤
            (3 / 4 : ℝ) * primeReciprocalMean S) := by
        simpa only [lowMediumDivisors] using hd
      have hd' : d ∈ Finset.Ioo n (2 * n) := (Finset.mem_filter.mp hdf).1
      have hdi := Finset.mem_Ioo.mp hd'
      have hmulti := (multipleCount_floor_bounds d x y (lt_trans hn hdi.1)).2
      have hdiv : y / d ≤ y / n :=
        Nat.div_le_div_left (Nat.le_of_lt hdi.1) hn
      exact le_trans (by simpa only [U, multipleCount] using hmulti)
        (Nat.add_le_add_right hdiv 1)
    _ = (lowMediumDivisors S n).card * (y / n + 1) := by simp

/-- Under the eventual linear-scale hypotheses, the low-divisor class costs at
most `64/μ` of the interval. -/
theorem lowDivisorCovered_weighted_linear_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) (n x y : ℕ)
    (hn : 0 < n) (hnQ : primeSquarePeriod S ≤ n)
    (hy : n * (primeSquarePeriod S + 2) ≤ y) :
    ((lowDivisorCovered S n x y).card : ℝ) * primeReciprocalMean S ≤
      64 * y := by
  have hcard := lowDivisorCovered_card_le S n x y hn
  have hdcount := lowMediumDivisors_weighted_bound S hprime hmu n
  have hcardR : ((lowDivisorCovered S n x y).card : ℝ) ≤
      (((lowMediumDivisors S n).card * (y / n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardR hmu.le
  have hfloor : n * (y / n) ≤ y := Nat.mul_div_le y n
  have hfloorR : (n : ℝ) * (y / n : ℕ) ≤ y := by exact_mod_cast hfloor
  have hyn : n ≤ y := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (primeSquarePeriod S + 2) :=
        Nat.mul_le_mul_left n (by omega)
      _ ≤ y := hy
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnQR : (primeSquarePeriod S : ℝ) ≤ n := by exact_mod_cast hnQ
  have hynR : (n : ℝ) ≤ y := by exact_mod_cast hyn
  calc
    ((lowDivisorCovered S n x y).card : ℝ) * primeReciprocalMean S
        ≤ ((lowMediumDivisors S n).card : ℝ) *
          ((y / n : ℕ) + 1) * primeReciprocalMean S := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using hmul
    _ = (((lowMediumDivisors S n).card : ℝ) * primeReciprocalMean S) *
          ((y / n : ℕ) + 1) := by ring
    _ ≤ (16 * (n + primeSquarePeriod S)) * ((y / n : ℕ) + 1) := by
      gcongr
    _ ≤ 64 * y := by
      nlinarith

/-- Consecutive candidate quotients for a divisor `d`. -/
def quotientRange (x y d : ℕ) : Finset ℕ :=
  Finset.Icc (x / d) ((x + y) / d)

lemma mem_quotientRange_of_dvd_mem_Ico {x y d m : ℕ}
    (hm : m ∈ Finset.Ico x (x + y)) (_hd : d ∣ m) :
    m / d ∈ quotientRange x y d := by
  rw [quotientRange, Finset.mem_Icc]
  have hlow : x / d ≤ m / d := Nat.div_le_div_right (Finset.mem_Ico.mp hm).1
  have hupp0 : m ≤ x + y := Nat.le_of_lt (Finset.mem_Ico.mp hm).2
  have hupp : m / d ≤ (x + y) / d := Nat.div_le_div_right hupp0
  exact ⟨hlow, hupp⟩

lemma quotientRange_eq_Ico (x y d : ℕ) :
    quotientRange x y d =
      Finset.Ico (x / d) (x / d + ((x + y) / d + 1 - x / d)) := by
  ext q
  simp only [quotientRange, Finset.mem_Icc, Finset.mem_Ico]
  have hxy : x / d ≤ (x + y) / d := Nat.div_le_div_right (Nat.le_add_right x y)
  omega

lemma quotientRange_length_le (x y d : ℕ) (hd : 0 < d) :
    (x + y) / d + 1 - x / d ≤ y / d + 2 := by
  have hupper : (x + y) / d ≤ x / d + y / d + 1 := by
    rw [Nat.add_div hd]
    split <;> omega
  have hlower : x / d ≤ (x + y) / d :=
    Nat.div_le_div_right (Nat.le_add_right x y)
  omega

/-- The low-quotient class costs at most `16(y+n(Q+2))/μ`. -/
theorem lowQuotientCovered_weighted_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) (n x y : ℕ) (hn : 0 < n) :
    ((lowQuotientCovered S n x y).card : ℝ) * primeReciprocalMean S ≤
      16 * (y + n * (primeSquarePeriod S + 2)) := by
  classical
  let D := Finset.Ioo n (2 * n)
  let C : ℕ → Finset ℕ := fun d => lowScoreSet S (quotientRange x y d)
  let PairSet : Finset (ℕ × ℕ) := D.biUnion fun d => (C d).image fun q => (d, q)
  have hcover : lowQuotientCovered S n x y ⊆
      PairSet.image (fun z => z.1 * z.2) := by
    intro m hm
    have hm' : m ∈ Finset.Ico x (x + y) ∧
        ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m ∧
          ¬(primeScore S d : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S ∧
          (primeScore S (m / d) : ℝ) ≤
            (3 / 4 : ℝ) * primeReciprocalMean S := by
      simpa only [lowQuotientCovered, Finset.mem_filter] using hm
    obtain ⟨d, hdD, hdm, hdgood, hqlow⟩ := hm'.2
    apply Finset.mem_image.mpr
    refine ⟨(d, m / d), ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨d, by simpa only [D] using hdD, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨m / d, ?_, rfl⟩
      have hqr := mem_quotientRange_of_dvd_mem_Ico hm'.1 hdm
      simpa only [C, lowScoreSet, Finset.mem_filter] using And.intro hqr hqlow
    · simp only
      exact Nat.mul_div_cancel' hdm
  have hcard : (lowQuotientCovered S n x y).card ≤
      ∑ d ∈ D, (C d).card := by
    calc
      (lowQuotientCovered S n x y).card
          ≤ (PairSet.image (fun z => z.1 * z.2)).card := Finset.card_le_card hcover
      _ ≤ PairSet.card := Finset.card_image_le
      _ ≤ ∑ d ∈ D, ((C d).image fun q => (d, q)).card := by
        exact Finset.card_biUnion_le
      _ = ∑ d ∈ D, (C d).card := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [Finset.card_image_iff.mpr]
        intro a _ha b _hb hab
        exact congrArg Prod.snd hab
  have hcand (d : ℕ) (hdD : d ∈ D) :
      ((C d).card : ℝ) * primeReciprocalMean S ≤
        16 * ((y / d + 2 + primeSquarePeriod S : ℕ) : ℝ) := by
    have hdI : d ∈ Finset.Ioo n (2 * n) := by simpa only [D] using hdD
    have hdpos : 0 < d := lt_trans hn (Finset.mem_Ioo.mp hdI).1
    let l := (x + y) / d + 1 - x / d
    have hi := low_primeScore_interval_bound S hprime hmu (x / d) l
    have heq := quotientRange_eq_Ico x y d
    have hlen := quotientRange_length_le x y d hdpos
    dsimp only [C]
    rw [heq]
    dsimp only [l] at hi
    exact le_trans hi (by
      have hlenR : ((l : ℕ) : ℝ) ≤ (y / d + 2 : ℕ) := by exact_mod_cast hlen
      push_cast at hlenR ⊢
      gcongr)
  have hsumWeighted :
      ((∑ d ∈ D, (C d).card : ℕ) : ℝ) * primeReciprocalMean S ≤
        ∑ d ∈ D, (16 : ℝ) * ((y / d + 2 + primeSquarePeriod S : ℕ) : ℝ) := by
    rw [Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum hcand
  have hsumDiv : ∑ d ∈ D, y / d ≤ y := by
    have hterm (d : ℕ) (hdD : d ∈ D) : y / d ≤ y / n := by
      have hdI : d ∈ Finset.Ioo n (2 * n) := by simpa only [D] using hdD
      exact Nat.div_le_div_left (Nat.le_of_lt (Finset.mem_Ioo.mp hdI).1) hn
    calc
      ∑ d ∈ D, y / d ≤ ∑ _d ∈ D, y / n := Finset.sum_le_sum hterm
      _ = D.card * (y / n) := by simp
      _ ≤ n * (y / n) := by
        gcongr
        dsimp only [D]
        rw [Nat.card_Ioo]
        omega
      _ ≤ y := Nat.mul_div_le y n
  have hDcard : D.card ≤ n := by
    dsimp only [D]
    rw [Nat.card_Ioo]
    omega
  have hsumBound :
      ∑ d ∈ D, (y / d + 2 + primeSquarePeriod S) ≤
        y + n * (primeSquarePeriod S + 2) := by
    calc
      ∑ d ∈ D, (y / d + 2 + primeSquarePeriod S) =
          (∑ d ∈ D, y / d) + D.card * (primeSquarePeriod S + 2) := by
        simp_rw [show ∀ d : ℕ, y / d + 2 + primeSquarePeriod S =
          y / d + (primeSquarePeriod S + 2) by intro; omega]
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ y + n * (primeSquarePeriod S + 2) := by gcongr
  have hcardR : ((lowQuotientCovered S n x y).card : ℝ) ≤
      ((∑ d ∈ D, (C d).card : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardR hmu.le
  calc
    ((lowQuotientCovered S n x y).card : ℝ) * primeReciprocalMean S
        ≤ ((∑ d ∈ D, (C d).card : ℕ) : ℝ) * primeReciprocalMean S := hmul
    _ ≤ ∑ d ∈ D, (16 : ℝ) *
        ((y / d + 2 + primeSquarePeriod S : ℕ) : ℝ) := hsumWeighted
    _ = 16 * ((∑ d ∈ D,
        (y / d + 2 + primeSquarePeriod S) : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ 16 * (y + n * (primeSquarePeriod S + 2)) := by
      have hsumBoundR :
          ((∑ d ∈ D, (y / d + 2 + primeSquarePeriod S) : ℕ) : ℝ) ≤
            (y + n * (primeSquarePeriod S + 2) : ℕ) := by exact_mod_cast hsumBound
      have hsumBoundR' :
          ((∑ d ∈ D, (y / d + 2 + primeSquarePeriod S) : ℕ) : ℝ) ≤
            (y : ℝ) + n * (primeSquarePeriod S + 2) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hsumBoundR
      exact mul_le_mul_of_nonneg_left hsumBoundR' (by norm_num)

/-- At scale `y ≥ n(Q+2)`, the low-quotient class costs at most `32y/μ`. -/
theorem lowQuotientCovered_weighted_linear_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) (n x y : ℕ) (hn : 0 < n)
    (hy : n * (primeSquarePeriod S + 2) ≤ y) :
    ((lowQuotientCovered S n x y).card : ℝ) * primeReciprocalMean S ≤
      32 * y := by
  have h := lowQuotientCovered_weighted_bound S hprime hmu n x y hn
  have hyR : ((n * (primeSquarePeriod S + 2) : ℕ) : ℝ) ≤ y := by
    exact_mod_cast hy
  push_cast at hyR
  exact le_trans h (by nlinarith)

/-- At the same scale, the high-square-score class costs at most `56y/μ`. -/
theorem highSquareScoreSet_weighted_linear_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S) (n x y : ℕ) (hn : 0 < n)
    (hy : n * (primeSquarePeriod S + 2) ≤ y) :
    ((highSquareScoreSet S (Finset.Ico x (x + y))).card : ℝ) *
        primeReciprocalMean S ≤ 56 * y := by
  have h := high_primeSquareScore_interval_bound S hprime hfive hmu x y
  have hQy : primeSquarePeriod S ≤ y := by
    calc
      primeSquarePeriod S ≤ primeSquarePeriod S + 2 := by omega
      _ = 1 * (primeSquarePeriod S + 2) := by omega
      _ ≤ n * (primeSquarePeriod S + 2) :=
        Nat.mul_le_mul_right (primeSquarePeriod S + 2) hn
      _ ≤ y := hy
  have hQyR : (primeSquarePeriod S : ℝ) ≤ y := by exact_mod_cast hQy
  simpa only [highSquareScoreSet] using le_trans h (by nlinarith)

/-- The finite-prime Turán decomposition gives a translate-uniform weighted
bound for all integers with a medium divisor. -/
theorem badFilter_Ico_weighted_linear_bound
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S) (n x y : ℕ) (hn : 0 < n)
    (hnQ : primeSquarePeriod S ≤ n)
    (hy : n * (primeSquarePeriod S + 2) ≤ y) :
    ((badFilter n (Finset.Ico x (x + y))).card : ℝ) *
        primeReciprocalMean S ≤ 152 * y := by
  have hsub := bad_filter_subset_turan_three_classes S n x y
  have hcard : (badFilter n (Finset.Ico x (x + y))).card ≤
      (lowDivisorCovered S n x y).card +
      (lowQuotientCovered S n x y).card +
      (highSquareScoreSet S (Finset.Ico x (x + y))).card := by
    calc
      (badFilter n (Finset.Ico x (x + y))).card
          ≤ ((lowDivisorCovered S n x y ∪ lowQuotientCovered S n x y) ∪
              highSquareScoreSet S (Finset.Ico x (x + y))).card :=
        Finset.card_le_card hsub
      _ ≤ (lowDivisorCovered S n x y ∪ lowQuotientCovered S n x y).card +
            (highSquareScoreSet S (Finset.Ico x (x + y))).card :=
        Finset.card_union_le _ _
      _ ≤ ((lowDivisorCovered S n x y).card +
            (lowQuotientCovered S n x y).card) +
            (highSquareScoreSet S (Finset.Ico x (x + y))).card := by
        gcongr
        exact Finset.card_union_le _ _
  have hcardR : ((badFilter n (Finset.Ico x (x + y))).card : ℝ) ≤
      (lowDivisorCovered S n x y).card +
      (lowQuotientCovered S n x y).card +
      (highSquareScoreSet S (Finset.Ico x (x + y))).card := by
    exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardR hmu.le
  have hlow := lowDivisorCovered_weighted_linear_bound
    S hprime hmu n x y hn hnQ hy
  have hquot := lowQuotientCovered_weighted_linear_bound
    S hprime hmu n x y hn hy
  have hhigh := highSquareScoreSet_weighted_linear_bound
    S hprime hfive hmu n x y hn hy
  nlinarith

/-- The weighted estimate implies the requested open-interval inequality whenever
the selected-prime reciprocal mass pays the constant `152/ε`. -/
theorem uniformlySparse_of_turan_budget
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S)
    (ε : ℝ) (hbudget : 152 ≤ ε * primeReciprocalMean S)
    (n y : ℕ) (hn : 0 < n) (hnQ : primeSquarePeriod S ≤ n)
    (hy : n * (primeSquarePeriod S + 2) ≤ y) :
    UniformlySparse ε n y := by
  intro x
  have hsub : badIntegers n x y ⊆
      badFilter n (Finset.Ico x (x + y)) := by
    intro m hm
    have hm' : m ∈ Finset.Ioo x (x + y) ∧ HasMediumDivisor n m := by
      simpa only [badIntegers, Finset.mem_filter] using hm
    have hi : m ∈ Finset.Ico x (x + y) := by
      exact Finset.mem_Ico.mpr ⟨Nat.le_of_lt (Finset.mem_Ioo.mp hm'.1).1,
        (Finset.mem_Ioo.mp hm'.1).2⟩
    have hmem : m ∈ Finset.Ico x (x + y) ∧ HasMediumDivisor n m := ⟨hi, hm'.2⟩
    simpa only [badFilter, Finset.mem_filter] using hmem
  have hcard : (localCount n x y : ℝ) ≤
      (badFilter n (Finset.Ico x (x + y))).card := by
    unfold localCount
    exact_mod_cast Finset.card_le_card hsub
  have hcardmu := mul_le_mul_of_nonneg_right hcard hmu.le
  have hweighted := badFilter_Ico_weighted_linear_bound
    S hprime hfive hmu n x y hn hnQ hy
  have hlocal : (localCount n x y : ℝ) * primeReciprocalMean S ≤ 152 * y :=
    le_trans hcardmu hweighted
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hpay : (152 : ℝ) * y ≤
      (ε * primeReciprocalMean S) * y :=
    mul_le_mul_of_nonneg_right hbudget hy0
  have hscaled : (localCount n x y : ℝ) * primeReciprocalMean S ≤
      (ε * y) * primeReciprocalMean S := by
    calc
      (localCount n x y : ℝ) * primeReciprocalMean S ≤ 152 * y := hlocal
      _ ≤ (ε * primeReciprocalMean S) * y := hpay
      _ = (ε * y) * primeReciprocalMean S := by ring
  exact le_of_mul_le_mul_right hscaled hmu

/-- The explicit linear coefficient attached to a fixed finite prime set. -/
def turanLinearScale (S : Finset ℕ) (n : ℕ) : ℕ :=
  n * (primeSquarePeriod S + 2)

/-- For one target `ε`, any selected-prime set with enough reciprocal mass
yields the claimed linear scale beyond its fixed square period. -/
theorem eventually_uniformlySparse_turanLinearScale_of_budget
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S)
    (ε : ℝ) (hbudget : 152 ≤ ε * primeReciprocalMean S) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : ℕ, turanLinearScale S n ≤ y → UniformlySparse ε n y := by
  refine ⟨max 1 (primeSquarePeriod S), ?_⟩
  intro n hn y hy
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) (le_trans (le_max_left _ _) hn)
  have hnQ : primeSquarePeriod S ≤ n := le_trans (le_max_right _ _) hn
  exact uniformlySparse_of_turan_budget S hprime hfive hmu ε
    hbudget n y hnpos hnQ hy

end Erdos450
