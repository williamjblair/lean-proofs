import Mathlib

/-!
# Two reflected owners give an exact small-defect relation

This file isolates the only genuinely global relation obtained by subtracting
two even-`k` reflected square lifts.  The products `Qᵢ ^ 2 * Uᵢ` may be
nonlinear, but their difference is exactly three times the owner separation.

The result deliberately has no Erdos-686 hypotheses: those hypotheses are
needed upstream to manufacture the two square-lift equalities.  Once the
equalities exist, the cancellation below is purely integral.
-/

namespace Erdos686LargeOwnerAggregation

/-- Ordered form of the two-owner small-defect identity.  The second
conclusion quantifies "small": for owners in `1, ..., k`, the defect is
strictly less than `3*k`. -/
theorem two_owner_small_defect_ordered
    (H n i j k Qi Qj Ui Uj : ℕ)
    (hi : Qi ^ 2 * Ui = H + 3 * (n + i))
    (hj : Qj ^ 2 * Uj = H + 3 * (n + j))
    (hiPos : 1 ≤ i)
    (hij : i ≤ j)
    (hjk : j ≤ k) :
    Qj ^ 2 * Uj = Qi ^ 2 * Ui + 3 * (j - i) ∧
      3 * (j - i) < 3 * k := by
  constructor <;> omega

/-- Signed form, convenient when the owners are not ordered in advance. -/
theorem two_owner_small_defect_int
    (H n i j Qi Qj Ui Uj : ℕ)
    (hi : Qi ^ 2 * Ui = H + 3 * (n + i))
    (hj : Qj ^ 2 * Uj = H + 3 * (n + j)) :
    (Qj ^ 2 * Uj : ℤ) - (Qi ^ 2 * Ui : ℤ) =
      3 * ((j : ℤ) - (i : ℤ)) := by
  have hiZ : (Qi : ℤ) ^ 2 * (Ui : ℤ) =
      (H : ℤ) + 3 * ((n : ℤ) + (i : ℤ)) := by
    exact_mod_cast hi
  have hjZ : (Qj : ℤ) ^ 2 * (Uj : ℤ) =
      (H : ℤ) + 3 * ((n : ℤ) + (j : ℤ)) := by
    exact_mod_cast hj
  rw [hiZ, hjZ]
  ring

#print axioms two_owner_small_defect_ordered
#print axioms two_owner_small_defect_int

end Erdos686LargeOwnerAggregation
