import Mathlib

namespace Erdos123

/-- Evaluation of a position-dependent digit code in ordinary radix `q`.
The actual digit selected at position `i` may be much larger than `q`; only its
residue will matter below. -/
def radixEval {q n : ℕ} (digit : Fin n → Fin q → ℕ)
    (word : Fin n → Fin q) : ℕ :=
  ∑ i : Fin n, q ^ (i : ℕ) * digit i (word i)

private theorem radixEval_succ {q n : ℕ}
    (digit : Fin (n + 1) → Fin q → ℕ)
    (word : Fin (n + 1) → Fin q) :
    radixEval digit word = digit 0 (word 0) +
      q * radixEval (fun i => digit i.succ) (fun i => word i.succ) := by
  rw [radixEval, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  rw [radixEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Fin.val_succ, pow_succ]
  ac_rfl

/-- If each position's actual digits have pairwise distinct residues modulo
`q`, then radix evaluation is injective modulo `q^n`. This remains true even
when the actual digits are large and position-dependent. -/
theorem radixEval_mod_injective {q n : ℕ} (hq : 1 < q)
    (digit : Fin n → Fin q → ℕ)
    (hdigit : ∀ i, Function.Injective (fun r => digit i r % q)) :
    Function.Injective (fun word : Fin n → Fin q => radixEval digit word % q ^ n) := by
  induction n with
  | zero =>
      intro x y _h
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro x y hxy
      have hmod : radixEval digit x ≡ radixEval digit y [MOD q ^ (n + 1)] := hxy
      have hmodq : radixEval digit x ≡ radixEval digit y [MOD q] :=
        hmod.of_dvd (by exact dvd_pow_self q (by omega : n + 1 ≠ 0))
      rw [radixEval_succ, radixEval_succ] at hmodq
      have hheadResidue : digit 0 (x 0) % q = digit 0 (y 0) % q := by
        simpa [Nat.ModEq] using hmodq
      have hhead : x 0 = y 0 := hdigit 0 hheadResidue
      have htailMod :
          radixEval (fun (i : Fin n) => digit i.succ)
              (fun (i : Fin n) => x i.succ) ≡
            radixEval (fun (i : Fin n) => digit i.succ)
              (fun (i : Fin n) => y i.succ) [MOD q ^ n] := by
        rw [radixEval_succ, radixEval_succ, hhead] at hmod
        have hcancelAdd :
            q * radixEval (fun (i : Fin n) => digit i.succ)
                (fun (i : Fin n) => x i.succ) ≡
              q * radixEval (fun (i : Fin n) => digit i.succ)
                (fun (i : Fin n) => y i.succ) [MOD q ^ (n + 1)] :=
          Nat.ModEq.add_left_cancel
            (Nat.ModEq.refl (digit 0 (y 0))) hmod
        have hpow : q ^ (n + 1) = q * q ^ n := by simp [pow_succ, Nat.mul_comm]
        rw [hpow] at hcancelAdd
        exact Nat.ModEq.mul_left_cancel' (by omega : q ≠ 0) hcancelAdd
      have htailEq : (fun (i : Fin n) => x i.succ) =
          (fun (i : Fin n) => y i.succ) := by
        apply ih (fun (i : Fin n) => digit i.succ)
          (fun (i : Fin n) => hdigit i.succ)
        exact htailMod
      funext i
      refine Fin.cases hhead ?_ i
      intro j
      exact congrFun htailEq j

end Erdos123
