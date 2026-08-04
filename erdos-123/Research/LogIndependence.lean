import Mathlib

namespace Erdos123

/-- Positive powers of coprime nontrivial natural numbers cannot coincide. -/
theorem coprime_pow_ne_pow {b c p q : ℕ}
    (hb : 1 < b) (hbc : Nat.Coprime b c) (hp : 0 < p) (hq : 0 < q) :
    b ^ p ≠ c ^ q := by
  intro heq
  have hbDiv : b ∣ c ^ q := by
    rw [← heq]
    exact dvd_pow_self b (by omega)
  have hbOne := (hbc.pow_right q).eq_one_of_dvd hbDiv
  omega

/-- The logarithms of coprime nontrivial integers have irrational ratio. -/
theorem irrational_log_ratio {b c : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hbc : Nat.Coprime b c) :
    Irrational (Real.log (b : ℝ) / Real.log (c : ℝ)) := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlogc : 0 < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  have hrPosReal : (0 : ℝ) < (r : ℝ) := by
    rw [hr]
    positivity
  have hrPos : (0 : ℚ) < r := Rat.cast_pos.mp hrPosReal
  have hnumPos : 0 < r.num := Rat.num_pos.mpr hrPos
  let p : ℕ := r.num.toNat
  let q : ℕ := r.den
  have hpPos : 0 < p := by
    dsimp [p]
    omega
  have hqPos : 0 < q := by
    exact r.den_pos
  have hpCast : ((p : ℕ) : ℝ) = (r.num : ℝ) := by
    have hnumNonneg : 0 ≤ r.num := by omega
    have hpInt : (p : ℤ) = r.num := by
      exact Int.toNat_of_nonneg hnumNonneg
    exact_mod_cast hpInt
  have hratio : Real.log (b : ℝ) / Real.log (c : ℝ) =
      (p : ℝ) / (q : ℝ) := by
    rw [← hr]
    rw [Rat.cast_def]
    simp only [q, hpCast]
  have hlogs : (q : ℝ) * Real.log (b : ℝ) =
      (p : ℝ) * Real.log (c : ℝ) := by
    field_simp [ne_of_gt hlogc, ne_of_gt (show (0 : ℝ) < q by exact_mod_cast hqPos)] at hratio
    nlinarith
  have hlogPowers : Real.log ((b : ℝ) ^ q) = Real.log ((c : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]
    exact hlogs
  have hpowersReal : (b : ℝ) ^ q = (c : ℝ) ^ p := by
    apply Real.log_injOn_pos
    · exact pow_pos (show (0 : ℝ) < (b : ℝ) by exact_mod_cast (show 0 < b by omega)) q
    · exact pow_pos (show (0 : ℝ) < (c : ℝ) by exact_mod_cast (show 0 < c by omega)) p
    · exact hlogPowers
  have hpowersNat : b ^ q = c ^ p := by exact_mod_cast hpowersReal
  exact coprime_pow_ne_pow hb hbc hqPos hpPos hpowersNat

end Erdos123
