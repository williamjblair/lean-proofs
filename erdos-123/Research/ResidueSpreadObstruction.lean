import Mathlib

namespace Erdos123

/-- A complete set of residue representatives modulo `q` cannot be packed into
an integer interval shorter than `q-1`. This is the sharp obstruction behind
the fact that a one-residue-at-a-time gluing step cannot amplify a mere pair
of consecutive subset sums. -/
theorem residue_representatives_interval_cardinality
    {q L U : ℕ} (hq : 0 < q) (hLU : L ≤ U)
    (z : Fin q → ℕ)
    (hzL : ∀ r, L ≤ z r) (hzU : ∀ r, z r ≤ U)
    (hzmod : ∀ r, z r % q = r.val) :
    q ≤ U - L + 1 := by
  let f : Fin q → {n // n ∈ Finset.Icc L U} := fun r =>
    ⟨z r, Finset.mem_Icc.mpr ⟨hzL r, hzU r⟩⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have hz : z r = z s := congrArg Subtype.val hrs
    apply Fin.ext
    rw [← hzmod r, ← hzmod s, hz]
  have hcard := Fintype.card_le_of_injective f hf
  have hcard' : q ≤ U + 1 - L := by simpa using hcard
  omega

/-- Equivalently, the numerical spread of any complete residue system is at
least `q-1`. -/
theorem residue_representatives_spread
    {q L U : ℕ} (hq : 0 < q) (hLU : L ≤ U)
    (z : Fin q → ℕ)
    (hzL : ∀ r, L ≤ z r) (hzU : ∀ r, z r ≤ U)
    (hzmod : ∀ r, z r % q = r.val) :
    q - 1 ≤ U - L := by
  have h := residue_representatives_interval_cardinality hq hLU z hzL hzU hzmod
  omega

/-- In the usual interval-gluing width formula `q*W-Δ`, the unavoidable
residue spread `Δ≥q-1` means that input width one can yield output width at
most one. -/
theorem one_width_cannot_amplify_by_complete_residues
    {q Δ : ℕ} (hq : 0 < q) (hspread : q - 1 ≤ Δ) :
    q * 1 - Δ ≤ 1 := by
  omega

end Erdos123
