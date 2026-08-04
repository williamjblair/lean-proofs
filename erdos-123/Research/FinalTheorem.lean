import Research.HomogeneousSeedInterval

namespace Erdos123

/-- Swapping the first two bases does not change the smooth set. -/
theorem smooth3_swap12 (a b c : ℕ) : Smooth3 a b c = Smooth3 b a c := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨j, i, k, by ac_rfl⟩
  · rintro ⟨j, i, k, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- Swapping the last two bases does not change the smooth set. -/
theorem smooth3_swap23 (a b c : ℕ) : Smooth3 a b c = Smooth3 a c b := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨i, k, j, by ac_rfl⟩
  · rintro ⟨i, k, j, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- A cyclic permutation does not change the smooth set. -/
theorem smooth3_cycle (a b c : ℕ) : Smooth3 a b c = Smooth3 b c a := by
  ext x
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨j, k, i, by ac_rfl⟩
  · rintro ⟨j, k, i, rfl⟩
    exact ⟨i, j, k, by ac_rfl⟩

/-- Every pairwise-coprime triple of bases greater than one is d-complete. -/
theorem intended_erdos_123 : IntendedStatement := by
  intro a b c ha hb hc hpw
  rcases hpw with ⟨hab, hac, hbc⟩
  have habne : a ≠ b := by
    intro heq
    subst b
    rw [Nat.coprime_self] at hab
    omega
  have hacne : a ≠ c := by
    intro heq
    subst c
    rw [Nat.coprime_self] at hac
    omega
  have hbcne : b ≠ c := by
    intro heq
    subst c
    rw [Nat.coprime_self] at hbc
    omega
  have horders :
      (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
      (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
      (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by
    omega
  rcases horders with habc | hacb | hbac | hbca | hcab | hcba
  · have h := ordered_three_base_is_dComplete ha hc hb
      habc.1 (habc.2) hac hab hbc.symm
    rw [smooth3_swap23] at h
    exact h
  · exact ordered_three_base_is_dComplete ha hb hc hacb.1 hacb.2 hab hac hbc
  · have h := ordered_three_base_is_dComplete hb hc ha
      hbac.1 hbac.2 hbc hab.symm hac.symm
    rw [show Smooth3 b c a = Smooth3 a b c by
      exact (smooth3_cycle a b c).symm] at h
    exact h
  · have h := ordered_three_base_is_dComplete hb ha hc
      hbca.1 hbca.2 hab.symm hbc hac
    rw [smooth3_swap12] at h
    exact h
  · have h := ordered_three_base_is_dComplete hc hb ha
      hcab.1 hcab.2 hbc.symm hac.symm hab.symm
    rw [show Smooth3 c b a = Smooth3 a b c by
      calc
        Smooth3 c b a = Smooth3 b a c := smooth3_cycle c b a
        _ = Smooth3 a b c := smooth3_swap12 b a c] at h
    exact h
  · have h := ordered_three_base_is_dComplete hc ha hb
      hcba.1 hcba.2 hac.symm hbc.symm hab
    rw [show Smooth3 c a b = Smooth3 a b c by exact smooth3_cycle c a b] at h
    exact h

end Erdos123
