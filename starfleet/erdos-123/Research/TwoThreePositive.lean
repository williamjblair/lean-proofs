import Research.InductionStep

namespace Erdos123

private theorem smooth23_pos {c x : ℕ} (hc : 0 < c)
    (hx : x ∈ Smooth3 2 3 c) : 0 < x := by
  rcases hx with ⟨i, j, k, rfl⟩
  exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    (pow_pos hc _)

private theorem scale_two_representable {c m : ℕ} (hc : 0 < c)
    (hm : IsRepresentable (Smooth3 2 3 c) m) :
    IsRepresentable (Smooth3 2 3 c) (2 * m) := by
  rcases hm with ⟨s, hsA, hsPrimitive, hsSum⟩
  have hsPos : ∀ x ∈ s, 0 < x := fun x hx => smooth23_pos hc (hsA x hx)
  have htPrimitive : IsPrimitive (∅ : Finset ℕ) := by simp [IsPrimitive]
  have htCoprime : ∀ y ∈ (∅ : Finset ℕ), Nat.Coprime 2 y := by simp
  have hsep : ∀ x ∈ s, ∀ y ∈ (∅ : Finset ℕ), x < y := by simp
  refine ⟨scaleFinset 2 s, ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases hsA x hx with ⟨i, j, k, rfl⟩
    refine ⟨i + 1, j, k, ?_⟩
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
  · simpa using isPrimitive_scaleFinset_union (by omega : 1 < 2) hsPos hsPrimitive
      htPrimitive htCoprime hsep
  · have hsum := sum_scaleFinset_union (s := s) (t := ∅)
      (by omega : 1 < 2) htCoprime
    simp only [Finset.union_empty, Finset.sum_empty, add_zero] at hsum
    rw [hsum, hsSum]

/-- Jansen--Lewin's induction: every natural number has a primitive
representation by `2^i 3^j` terms. We state it inside any three-base system by
setting the third exponent to zero. -/
theorem every_nat_representable_by_two_three (c n : ℕ) (hc : 0 < c) :
    IsRepresentable (Smooth3 2 3 c) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        refine ⟨∅, ?_, ?_, ?_⟩ <;> simp [IsPrimitive]
      by_cases heven : 2 ∣ n
      · let m := n / 2
        have htwo : 2 * m = n := Nat.mul_div_cancel' heven
        have hmLt : m < n := by
          have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
          rw [← htwo]
          have hmPos : 0 < m := by
            by_contra hm0
            have : m = 0 := Nat.eq_zero_of_not_pos hm0
            rw [this, mul_zero] at htwo
            omega
          simpa using Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2) hmPos
        rw [← htwo]
        exact scale_two_representable hc (ih m hmLt)
      · have hnOdd : n % 2 = 1 := by omega
        let p := Nat.log 3 n
        let q := 3 ^ p
        have hqLe : q ≤ n := by
          dsimp [q, p]
          exact Nat.pow_log_le_self 3 hn0
        have hnLt3q : n < 3 * q := by
          have h := Nat.lt_pow_succ_log_self (by omega : 1 < 3) n
          simpa [q, p, pow_succ, mul_comm] using h
        by_cases hnq : n = q
        · refine ⟨{q}, ?_, ?_, ?_⟩
          · intro x hx
            simp only [Finset.mem_singleton] at hx
            subst x
            exact ⟨0, p, 0, by simp [q]⟩
          · simp [IsPrimitive]
          · simpa [hnq]
        · have hqLt : q < n := lt_of_le_of_ne hqLe (Ne.symm hnq)
          have hdiffEven : 2 ∣ n - q := by
            have hqOdd : q % 2 = 1 := by
              exact Nat.odd_iff.mp ((by norm_num : Odd 3).pow)
            exact Nat.dvd_of_mod_eq_zero (by omega)
          let m := (n - q) / 2
          have h2m : 2 * m = n - q := Nat.mul_div_cancel' hdiffEven
          have hnEq : n = 2 * m + q := by rw [h2m]; omega
          have hmLtQ : m < q := by nlinarith
          have hmLtN : m < n := hmLtQ.trans hqLt
          rcases ih m hmLtN with ⟨s, hsA, hsPrimitive, hsSum⟩
          have hsPos : ∀ x ∈ s, 0 < x := fun x hx => smooth23_pos hc (hsA x hx)
          have hqPos : 0 < q := by positivity
          have hqCoprime : Nat.Coprime 2 q :=
            Nat.coprime_two_left.mpr ((by norm_num : Odd 3).pow)
          have hsep : ∀ x ∈ s, ∀ y ∈ ({q} : Finset ℕ), x < y := by
            intro x hx y hy
            simp only [Finset.mem_singleton] at hy
            subst y
            have hxLe : x ≤ m := by
              rw [← hsSum]
              simpa only [id_eq] using
                Finset.single_le_sum (fun z _hz => Nat.zero_le z) hx
            exact hxLe.trans_lt hmLtQ
          refine ⟨scaleFinset 2 s ∪ {q}, ?_,
            isPrimitive_scaleFinset_union (by omega : 1 < 2) hsPos hsPrimitive
              (by simp [IsPrimitive]) (by
                intro y hy
                simp only [Finset.mem_singleton] at hy
                subst y
                exact hqCoprime) hsep, ?_⟩
          · intro y hy
            rcases Finset.mem_union.mp hy with hyOld | hyQ
            · rcases Finset.mem_image.mp hyOld with ⟨x, hx, rfl⟩
              rcases hsA x hx with ⟨i, j, k, rfl⟩
              refine ⟨i + 1, j, k, ?_⟩
              simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
            · simp only [Finset.mem_singleton] at hyQ
              subst y
              exact ⟨0, p, 0, by simp [q]⟩
          · rw [sum_scaleFinset_union (by omega : 1 < 2)
              (by
                intro y hy
                simp only [Finset.mem_singleton] at hy
                subst y
                exact hqCoprime), hsSum]
            simp only [Finset.sum_singleton, id_eq]
            exact hnEq.symm

/-- Any pairwise-coprime triple containing `2` and `3` (in this order) satisfies
the full target conclusion, indeed with threshold zero. -/
theorem two_three_c_is_dComplete (c : ℕ) (hc : 0 < c) :
    IsDComplete (Smooth3 2 3 c) := by
  exact ⟨0, fun n _hn => every_nat_representable_by_two_three c n hc⟩

private theorem smooth3_perm_abc_acb (a b c : ℕ) :
    Smooth3 a b c = Smooth3 a c b := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨i, k, j, by ac_rfl⟩
  · rintro ⟨i, k, j, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

private theorem smooth3_perm_abc_bac (a b c : ℕ) :
    Smooth3 a b c = Smooth3 b a c := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨j, i, k, by ac_rfl⟩
  · rintro ⟨j, i, k, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- The same complete `(2,3)` subsystem works in any of the six orders of the
three bases. -/
theorem unordered_two_three_is_dComplete (a b c : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c)
    (h23 : (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
      (a = 2 ∧ c = 3) ∨ (a = 3 ∧ c = 2) ∨
      (b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) :
    IsDComplete (Smooth3 a b c) := by
  rcases h23 with hab | hab | hac | hac | hbc | hbc
  · rcases hab with ⟨rfl, rfl⟩
    exact two_three_c_is_dComplete c hc
  · rcases hab with ⟨rfl, rfl⟩
    rw [smooth3_perm_abc_bac]
    exact two_three_c_is_dComplete c hc
  · rcases hac with ⟨rfl, rfl⟩
    rw [smooth3_perm_abc_acb]
    exact two_three_c_is_dComplete b hb
  · rcases hac with ⟨rfl, rfl⟩
    rw [show Smooth3 3 b 2 = Smooth3 2 3 b by
      ext x
      constructor
      · rintro ⟨i, j, k, rfl⟩
        exact ⟨k, i, j, by ac_rfl⟩
      · rintro ⟨k, i, j, rfl⟩
        exact ⟨i, j, k, by ac_rfl⟩]
    exact two_three_c_is_dComplete b hb
  · rcases hbc with ⟨rfl, rfl⟩
    rw [show Smooth3 a 2 3 = Smooth3 2 3 a by
      ext x
      constructor
      · rintro ⟨i, j, k, rfl⟩
        exact ⟨j, k, i, by ac_rfl⟩
      · rintro ⟨j, k, i, rfl⟩
        exact ⟨i, j, k, by ac_rfl⟩]
    exact two_three_c_is_dComplete a ha
  · rcases hbc with ⟨rfl, rfl⟩
    rw [show Smooth3 a 3 2 = Smooth3 2 3 a by
      ext x
      constructor
      · rintro ⟨i, j, k, rfl⟩
        exact ⟨k, j, i, by ac_rfl⟩
      · rintro ⟨k, j, i, rfl⟩
        exact ⟨i, j, k, by ac_rfl⟩]
    exact two_three_c_is_dComplete a ha

end Erdos123
