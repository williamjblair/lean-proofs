import Mathlib

#check Rat.num_div_den
#check Rat.normalize_num_den
#check Rat.den_nz
#check Rat.den_pos
#check Rat.divInt_eq_div
#check Nat.mul_div_left
#check Nat.mul_div_right
#check Finset.dvd_prod_of_mem

def clearRat (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

theorem clearRat_cast {D : ℕ} {q : ℚ} (h : q.den ∣ D) :
    (clearRat D q : ℚ) = (D : ℚ) * q := by
  obtain ⟨t, rfl⟩ := h
  calc
    (clearRat (q.den * t) q : ℚ) =
        ((q.den * t : ℕ) : ℚ) *
          ((q.num : ℚ) / (q.den : ℚ)) := by
            simp only [clearRat]
            rw [Nat.mul_div_right t q.den_pos]
            push_cast
            field_simp [q.den_nz]
    _ = ((q.den * t : ℕ) : ℚ) * q := by rw [q.num_div_den]
