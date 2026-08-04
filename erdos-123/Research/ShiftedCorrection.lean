import Research.CorrectionGadget
import Research.InductionStep

namespace Erdos123

/-- A common `b,c`-smooth scale which remains one modulo `a`. -/
def correctionMultiplier (a b c u v : ℕ) : ℕ :=
  b ^ (a.totient * u) * c ^ (a.totient * v)

/-- A residue gadget shifted to a desired multiplicative scale. -/
def shiftedCorrectionSet (a b c r u v : ℕ) : Finset ℕ :=
  scaleFinset (correctionMultiplier a b c u v) (correctionSet a b c r)

theorem correctionMultiplier_modEq_one {a b c u v : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) :
    correctionMultiplier a b c u v ≡ 1 [MOD a] := by
  have hb : b ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hab.symm
  have hc : c ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hac.symm
  simpa [correctionMultiplier, pow_mul] using (hb.pow u).mul (hc.pow v)

theorem correctionMultiplier_pos {a b c u v : ℕ} (hb : 1 < b) (hc : 1 < c) :
    0 < correctionMultiplier a b c u v := by
  simp [correctionMultiplier, pow_pos (by omega : 0 < b), pow_pos (by omega : 0 < c)]

private theorem correctionTerm_pos {a b c r t : ℕ} (hb : 1 < b) (hc : 1 < c) :
    0 < correctionTerm a b c r t := by
  simp [correctionTerm, pow_pos (by omega : 0 < b), pow_pos (by omega : 0 < c)]

/-- Every shifted correction term is at least its common multiplier. -/
theorem correctionMultiplier_le_of_mem_shifted {a b c r u v y : ℕ}
    (hb : 1 < b) (hc : 1 < c)
    (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    correctionMultiplier a b c u v ≤ y := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  exact Nat.le_mul_of_pos_right _ (correctionTerm_pos hb hc)

/-- Common scaling preserves the gadget antichain. -/
theorem shiftedCorrectionSet_isPrimitive {a b c r u v : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsPrimitive (shiftedCorrectionSet a b c r u v) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
  intro hdvd
  apply (correctionSet_isPrimitive ha hb hc hab hac hbc) hx₀ hy₀
  · intro heq
    subst y₀
    exact hxy rfl
  · exact (Nat.mul_dvd_mul_iff_left (correctionMultiplier_pos hb hc)).mp hdvd

/-- Exact shifted-gadget sum. -/
theorem shiftedCorrectionSet_sum {a b c r u v : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (shiftedCorrectionSet a b c r u v).sum id =
      correctionMultiplier a b c u v * (correctionSet a b c r).sum id := by
  unfold shiftedCorrectionSet scaleFinset
  have hinj : Set.InjOn (fun x : ℕ => correctionMultiplier a b c u v * x)
      (correctionSet a b c r : Set ℕ) := by
    intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left (correctionMultiplier_pos hb hc) hxy
  rw [Finset.sum_image hinj]
  simpa only [id_eq] using
    (Finset.mul_sum (correctionSet a b c r) id (correctionMultiplier a b c u v)).symm

/-- Every shifted correction term is coprime to `a`. -/
theorem shiftedCorrectionSet_coprime {a b c r u v y : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c)
    (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    Nat.Coprime a y := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  unfold correctionMultiplier correctionTerm
  exact (((hab.pow_right _).mul_right (hac.pow_right _)).mul_right
    ((hab.pow_right _).mul_right (hac.pow_right _)))

/-- The shifted correction sum retains residue `r` modulo `a`. -/
theorem shiftedCorrectionSet_sum_modEq {a b c r u v : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    (shiftedCorrectionSet a b c r u v).sum id ≡ r [MOD a] := by
  rw [shiftedCorrectionSet_sum ha hb hc]
  simpa using (correctionMultiplier_modEq_one (u := u) (v := v) hab hac).mul
    (correctionSet_sum_modEq (r := r) ha hb hc hab hac hbc)

/-- Every shifted correction term belongs to the original three-base smooth set. -/
theorem shiftedCorrectionSet_subset_smooth3 {a b c r u v : ℕ}
    {y : ℕ} (hy : y ∈ shiftedCorrectionSet a b c r u v) :
    y ∈ Smooth3 a b c := by
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
  refine ⟨0, a.totient * u + a.totient * t,
    a.totient * v + a.totient * (r - 1 - t), ?_⟩
  simp [correctionMultiplier, correctionTerm, pow_add, mul_assoc, mul_comm, mul_left_comm]

end Erdos123
