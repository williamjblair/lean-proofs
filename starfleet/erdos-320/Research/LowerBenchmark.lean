import Research.LowerMesh

/-! # Continuous-scale lower benchmark on the exact logarithmic mesh -/

namespace Research

/-- Lower benchmark chosen so division by the renewal kernel dominates the
right-endpoint logarithmic mesh. -/
noncomputable def lowerRenewalBenchmark (k n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / Real.log n *
    clampedIteratedLogProduct k (logLogNat (n + 1))

/-- The lower benchmark is nonnegative on its natural range. -/
theorem lowerRenewalBenchmark_nonneg (k n : ℕ) (hn : 2 ≤ n) :
    0 ≤ lowerRenewalBenchmark k n := by
  rw [lowerRenewalBenchmark]
  exact mul_nonneg (div_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
    (clampedIteratedLogProduct_nonneg k _)

/-- Each weighted lower benchmark term dominates the corresponding right
mesh cell. -/
theorem right_mesh_term_le_lowerRenewalBenchmark_div
    (k n : ℕ) (hn : 2 ≤ n) :
    clampedIteratedLogProduct k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      lowerRenewalBenchmark k n / ((n : ℝ) * (n + 1)) := by
  have hmesh := logLogNat_sub_le_one_div_mul_log n hn
  have hP := clampedIteratedLogProduct_nonneg k (logLogNat (n + 1))
  have hnR : (0 : ℝ) < n := by positivity
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  calc
    clampedIteratedLogProduct k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      clampedIteratedLogProduct k (logLogNat (n + 1)) *
        (1 / ((n : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hmesh hP
    _ = lowerRenewalBenchmark k n / ((n : ℝ) * (n + 1)) := by
      rw [lowerRenewalBenchmark]
      field_simp
      norm_num only [Nat.cast_add, Nat.cast_one]

/-- Summed specialization: a high power tail yields almost the full next
iterated-log factor. -/
theorem iteratedLogProduct_le_lowerBenchmark_transform
    (k y : ℕ) (e : ℝ) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : realTower 2 k ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y *
        iteratedLogProduct k (logLogNat y) ≤
      ∑ n ∈ Finset.Ico 2 y,
        lowerRenewalBenchmark k n / ((n : ℝ) * (n + 1)) := by
  apply le_trans (iteratedLogProduct_right_mesh_lower k y e hy he0 he2
    hx1 htlow htower hratio horbit)
  apply Finset.sum_le_sum
  intro n hn
  exact right_mesh_term_le_lowerRenewalBenchmark_div k n
    (Finset.mem_Ico.mp hn).1

/-- Benchmark with a prescribed high tower cutoff. -/
noncomputable def highLowerRenewalBenchmark (H : ℝ) (k n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / Real.log n *
    cutoffIteratedLogProduct H k (logLogNat (n + 1))

/-- It is nonnegative for `H≥2`. -/
theorem highLowerRenewalBenchmark_nonneg {H : ℝ} (hH : 2 ≤ H)
    (k n : ℕ) (hn : 2 ≤ n) :
    0 ≤ highLowerRenewalBenchmark H k n := by
  rw [highLowerRenewalBenchmark]
  exact mul_nonneg (div_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
    (cutoffIteratedLogProduct_nonneg hH k _)

/-- Its weighted term dominates the high-cutoff right mesh cell. -/
theorem right_mesh_term_le_highLowerRenewalBenchmark_div
    {H : ℝ} (hH : 2 ≤ H) (k n : ℕ) (hn : 2 ≤ n) :
    cutoffIteratedLogProduct H k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      highLowerRenewalBenchmark H k n / ((n : ℝ) * (n + 1)) := by
  have hmesh := logLogNat_sub_le_one_div_mul_log n hn
  have hP := cutoffIteratedLogProduct_nonneg hH k (logLogNat (n + 1))
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  calc
    cutoffIteratedLogProduct H k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      cutoffIteratedLogProduct H k (logLogNat (n + 1)) *
        (1 / ((n : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hmesh hP
    _ = highLowerRenewalBenchmark H k n / ((n : ℝ) * (n + 1)) := by
      rw [highLowerRenewalBenchmark]
      field_simp
      norm_num only [Nat.cast_add, Nat.cast_one]

/-- High-cutoff summed transform. -/
theorem iteratedLogProduct_le_highLowerBenchmark_transform
    (H : ℝ) (k y : ℕ) (e : ℝ) (hH : 2 ≤ H) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : realTower H k ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y * iteratedLogProduct k (logLogNat y) ≤
      ∑ n ∈ Finset.Ico 2 y,
        highLowerRenewalBenchmark H k n / ((n : ℝ) * (n + 1)) := by
  apply le_trans (iteratedLogProduct_cutoff_right_mesh_lower H k y e hH hy
    he0 he2 hx1 htlow htower hratio horbit)
  apply Finset.sum_le_sum
  intro n hn
  exact right_mesh_term_le_highLowerRenewalBenchmark_div hH k n
    (Finset.mem_Ico.mp hn).1

/-- Benchmark with an arbitrary height-dependent cutoff sequence. -/
noncomputable def adaptiveLowerRenewalBenchmark (R : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / Real.log n *
    cutoffAtIteratedLogProduct (R k) k (logLogNat (n + 1))

theorem adaptiveLowerRenewalBenchmark_nonneg {R : ℕ → ℝ} {k : ℕ}
    (hfloor : realTower 2 k ≤ R k) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ adaptiveLowerRenewalBenchmark R k n := by
  rw [adaptiveLowerRenewalBenchmark]
  exact mul_nonneg (div_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
    (cutoffAtIteratedLogProduct_nonneg hfloor _)

/-- Weighted adaptive benchmark term dominates its right mesh cell. -/
theorem right_mesh_term_le_adaptiveLowerRenewalBenchmark_div
    {R : ℕ → ℝ} {k : ℕ} (hfloor : realTower 2 k ≤ R k)
    (n : ℕ) (hn : 2 ≤ n) :
    cutoffAtIteratedLogProduct (R k) k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      adaptiveLowerRenewalBenchmark R k n / ((n : ℝ) * (n + 1)) := by
  have hmesh := logLogNat_sub_le_one_div_mul_log n hn
  have hP := cutoffAtIteratedLogProduct_nonneg hfloor (logLogNat (n + 1))
  calc
    cutoffAtIteratedLogProduct (R k) k (logLogNat (n + 1)) *
        (logLogNat (n + 1) - logLogNat n) ≤
      cutoffAtIteratedLogProduct (R k) k (logLogNat (n + 1)) *
        (1 / ((n : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hmesh hP
    _ = adaptiveLowerRenewalBenchmark R k n / ((n : ℝ) * (n + 1)) := by
      rw [adaptiveLowerRenewalBenchmark]
      field_simp
      norm_num only [Nat.cast_add, Nat.cast_one]

/-- Adaptive-cutoff summed transform. -/
theorem iteratedLogProduct_le_adaptiveLowerBenchmark_transform
    (R : ℕ → ℝ) (k y : ℕ) (e : ℝ)
    (hfloor : realTower 2 k ≤ R k) (hy : 3 ≤ y)
    (he0 : 0 < e) (he2 : e ≤ 1 / 2)
    (hx1 : 1 < logLogNat y)
    (htlow : logLogNat 2 ≤ logLogNat y ^ (1 - e))
    (htower : R k ≤ logLogNat y ^ (1 - e))
    (hratio : logLogNat y ^ (1 - e) ≤ e * logLogNat y)
    (horbit : ∀ j, 1 ≤ j → j ≤ k →
      2 ≤ iteratedLog j (logLogNat y)) :
    (1 - e) ^ (k + 1) * logLogNat y * iteratedLogProduct k (logLogNat y) ≤
      ∑ n ∈ Finset.Ico 2 y,
        adaptiveLowerRenewalBenchmark R k n / ((n : ℝ) * (n + 1)) := by
  apply le_trans (iteratedLogProduct_cutoffAt_right_mesh_lower (R k) k y e
    hfloor hy he0 he2 hx1 htlow htower hratio horbit)
  apply Finset.sum_le_sum
  intro n hn
  exact right_mesh_term_le_adaptiveLowerRenewalBenchmark_div hfloor n
    (Finset.mem_Ico.mp hn).1

end Research
