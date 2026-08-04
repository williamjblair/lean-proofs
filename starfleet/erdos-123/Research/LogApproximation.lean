import Research.LogIndependence

namespace Erdos123

/-- Integer linear combinations of the two logarithms occur in every positive
neighborhood of zero. -/
theorem exists_small_positive_log_combination {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < m • Real.log (b : ℝ) + n • Real.log (c : ℝ) ∧
      m • Real.log (b : ℝ) + n • Real.log (c : ℝ) < ε := by
  have hirr := irrational_log_ratio hb hc hbc
  have hdense : Dense (AddSubgroup.closure
      ({Real.log (b : ℝ), Real.log (c : ℝ)} : Set ℝ) : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff).mpr hirr
  rcases hdense.exists_between hε with ⟨z, hz, hz0, hzε⟩
  rcases AddSubgroup.mem_closure_pair.mp hz with ⟨m, n, rfl⟩
  exact ⟨m, n, hz0, hzε⟩

/-- There are positive powers of `b` and `c` whose logarithms differ, in
one orientation or the other, by any prescribed positive amount. -/
theorem exists_close_power_logs {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ((0 < (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ) ∧
          (p : ℝ) * Real.log (b : ℝ) - (q : ℝ) * Real.log (c : ℝ) < ε) ∨
       (0 < (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ) ∧
          (q : ℝ) * Real.log (c : ℝ) - (p : ℝ) * Real.log (b : ℝ) < ε)) := by
  have hlb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlc : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  let δ : ℝ := min ε (min (Real.log (b : ℝ)) (Real.log (c : ℝ)))
  have hδ : 0 < δ := by simp [δ, hε, hlb, hlc]
  have hδε : δ ≤ ε := min_le_left _ _
  have hδb : δ ≤ Real.log (b : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ Real.log (c : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  rcases exists_small_positive_log_combination hb hc hbc hδ with
    ⟨m, n, hz0, hzδ⟩
  simp only [zsmul_eq_mul] at hz0 hzδ
  have hzε : (m : ℝ) * Real.log (b : ℝ) + (n : ℝ) * Real.log (c : ℝ) < ε :=
    hzδ.trans_le hδε

  rcases lt_trichotomy m 0 with hmneg | rfl | hmpos
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ (-1 : ℤ) by omega)
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
      nlinarith
    · simp only [Int.cast_zero, zero_mul, add_zero] at hz0
      have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ (-1 : ℤ) by omega)
      nlinarith
    · let p : ℕ := (-m).toNat
      let q : ℕ := n.toNat
      have hpInt : (p : ℤ) = -m := by
        exact Int.toNat_of_nonneg (by omega)
      have hqInt : (q : ℤ) = n := by
        exact Int.toNat_of_nonneg (by omega)
      have hpReal : (p : ℝ) = -(m : ℝ) := by exact_mod_cast hpInt
      have hqReal : (q : ℝ) = (n : ℝ) := by exact_mod_cast hqInt
      refine ⟨p, q, ?_, ?_, Or.inr ?_⟩
      · dsimp [p]
        omega
      · dsimp [q]
        omega
      · rw [hpReal, hqReal]
        constructor <;> nlinarith
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · simp only [Int.cast_zero, zero_mul, zero_add] at hz0
      have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
      nlinarith
    · norm_num at hz0
    · simp only [Int.cast_zero, zero_mul, zero_add] at hzδ
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      nlinarith
  · rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
    · let p : ℕ := m.toNat
      let q : ℕ := (-n).toNat
      have hpInt : (p : ℤ) = m := by
        exact Int.toNat_of_nonneg (by omega)
      have hqInt : (q : ℤ) = -n := by
        exact Int.toNat_of_nonneg (by omega)
      have hpReal : (p : ℝ) = (m : ℝ) := by exact_mod_cast hpInt
      have hqReal : (q : ℝ) = -(n : ℝ) := by exact_mod_cast hqInt
      refine ⟨p, q, ?_, ?_, Or.inl ?_⟩
      · dsimp [p]
        omega
      · dsimp [q]
        omega
      · rw [hpReal, hqReal]
        constructor <;> nlinarith
    · simp only [Int.cast_zero, zero_mul, add_zero] at hzδ
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      nlinarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      nlinarith

/-- Arbitrarily close unequal powers exist: in one orientation, the larger of
`b^p,c^q` is less than `ρ` times the smaller. -/
theorem exists_close_powers {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c)
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ((((c : ℝ) ^ q < (b : ℝ) ^ p) ∧
          (b : ℝ) ^ p < ρ * (c : ℝ) ^ q) ∨
       (((b : ℝ) ^ p < (c : ℝ) ^ q) ∧
          (c : ℝ) ^ q < ρ * (b : ℝ) ^ p)) := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hρpos : 0 < ρ := by linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  rcases exists_close_power_logs hb hc hbc hlogρ with
    ⟨p, q, hp, hq, hdir | hdir⟩
  · refine ⟨p, q, hp, hq, Or.inl ⟨?_, ?_⟩⟩
    · apply (Real.strictMonoOn_log.lt_iff_lt
        (pow_pos hcpos q) (pow_pos hbpos p)).mp
      rw [Real.log_pow, Real.log_pow]
      nlinarith [hdir.1]
    · apply (Real.strictMonoOn_log.lt_iff_lt
        (pow_pos hbpos p)
        (mul_pos hρpos (pow_pos hcpos q))).mp
      rw [Real.log_pow, Real.log_mul (ne_of_gt hρpos) (ne_of_gt (pow_pos hcpos q)),
        Real.log_pow]
      nlinarith [hdir.2]
  · refine ⟨p, q, hp, hq, Or.inr ⟨?_, ?_⟩⟩
    · apply (Real.strictMonoOn_log.lt_iff_lt
        (pow_pos hbpos p) (pow_pos hcpos q)).mp
      rw [Real.log_pow, Real.log_pow]
      nlinarith [hdir.1]
    · apply (Real.strictMonoOn_log.lt_iff_lt
        (pow_pos hcpos q)
        (mul_pos hρpos (pow_pos hbpos p))).mp
      rw [Real.log_pow, Real.log_mul (ne_of_gt hρpos) (ne_of_gt (pow_pos hbpos p)),
        Real.log_pow]
      nlinarith [hdir.2]

end Erdos123
