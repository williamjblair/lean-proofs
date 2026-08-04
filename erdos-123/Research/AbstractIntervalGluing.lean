import Mathlib

namespace Erdos123

/-- Abstract arithmetic core of residue-based interval gluing. `Old m` means
that the recursive target `m` is available, `Corr z` that a correction of sum
`z` is available, and `New n` that they can be glued to form `n=q*m+z`. -/
theorem abstract_interval_gluing
    {q L U Zlo Zhi : ℕ} {Old Corr New : ℕ → Prop}
    (hq : 0 < q) (hLU : L ≤ U) (hZ : Zlo ≤ Zhi)
    (hOld : ∀ m, L ≤ m → m ≤ U → Old m)
    (hCorr : ∀ r < q, ∃ z, Zlo ≤ z ∧ z ≤ Zhi ∧ z % q = r)
    (hglue : ∀ m z, Old m → Corr z → New (q * m + z))
    (hCorrAvailable : ∀ z, Zlo ≤ z → z ≤ Zhi → Corr z) :
    ∀ n, q * L + Zhi ≤ n → n ≤ q * U + Zlo → New n := by
  intro n hnLo hnHi
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  rcases hCorr r hr with ⟨z, hzLo, hzHi, hzmod⟩
  have hzLeN : z ≤ n := by omega
  have hnmod : n ≡ r [MOD q] := by
    show n % q = r % q
    simp [r, Nat.mod_eq_of_lt hr]
  have hzmod' : z ≡ r [MOD q] := by
    show z % q = r % q
    simp [hzmod, Nat.mod_eq_of_lt hr]
  have hsubmod : n - z ≡ 0 [MOD q] := by
    simpa using hnmod.sub hzLeN (le_refl r) hzmod'
  have hdiv : q ∣ n - z := Nat.modEq_zero_iff_dvd.mp hsubmod
  let m := (n - z) / q
  have hqm : q * m = n - z := Nat.mul_div_cancel' hdiv
  have hnEq : n = q * m + z := by rw [hqm]; omega
  have hmLo : L ≤ m := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    rw [mul_comm]
    omega
  have hmHi : m ≤ U := by
    apply Nat.le_of_mul_le_mul_left (c := q) _ hq
    rw [hqm]
    omega
  rw [hnEq]
  exact hglue m z (hOld m hmLo hmHi) (hCorrAvailable z hzLo hzHi)

/-- Numerical width furnished by the abstract gluing interval. -/
theorem abstract_gluing_width
    {q L U Zlo Zhi : ℕ} (hLU : L ≤ U) (hZ : Zlo ≤ Zhi)
    (hnonempty : q * L + Zhi ≤ q * U + Zlo) :
    (q * U + Zlo) - (q * L + Zhi) =
      q * (U - L) - (Zhi - Zlo) := by
  rw [Nat.mul_sub_left_distrib]
  omega

end Erdos123
