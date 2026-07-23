import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- The closed planar cone used in the record argument: `(u,v)` lies in it iff `u ≥ |v|`. -/
def InCone (z : ℝ × ℝ) : Prop := |z.2| ≤ z.1

@[simp] lemma inCone_zero : InCone (0 : ℝ × ℝ) := by simp [InCone]

lemma InCone.add {z w : ℝ × ℝ} (hz : InCone z) (hw : InCone w) : InCone (z + w) := by
  rw [InCone] at hz hw ⊢
  dsimp only [Prod.fst_add, Prod.snd_add]
  exact (abs_add_le _ _).trans (add_le_add hz hw)

/-- Walk position after the first `n` increments (so `walk z 0 = 0`). -/
def walk (z : ℕ → ℝ × ℝ) (n : ℕ) : ℝ × ℝ :=
  ∑ i ∈ Finset.range n, z i

/-- Time `n` is a cone record when every suffix ending at `n` lies in the cone. -/
def IsConeRecord (z : ℕ → ℝ × ℝ) (n : ℕ) : Prop :=
  ∀ k < n, InCone (walk z n - walk z k)

/-- Only the suffixes beginning at or after time `a` are tested at time `b`. -/
def IsConeRecordAfter (z : ℕ → ℝ × ℝ) (a b : ℕ) : Prop :=
  ∀ k, a ≤ k → k < b → InCone (walk z b - walk z k)

/-- Exact deterministic record decomposition.  Once `a` is a cone record, checking that `b` is
a cone record only requires the fresh suffixes beginning at or after `a`. -/
lemma cone_record_decomposition (z : ℕ → ℝ × ℝ) {a b : ℕ} (hab : a < b) :
    IsConeRecord z a ∧ IsConeRecordAfter z a b ↔
      IsConeRecord z a ∧ IsConeRecord z b := by
  constructor
  · rintro ⟨ha, hbFresh⟩
    refine ⟨ha, ?_⟩
    intro k hkb
    by_cases hka : k < a
    · have hba := hbFresh a le_rfl hab
      have hak := ha k hka
      have hid : walk z b - walk z k =
          (walk z b - walk z a) + (walk z a - walk z k) := by
        abel
      rw [hid]
      exact hba.add hak
    · exact hbFresh k (Nat.le_of_not_gt hka) hkb
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    intro k hka hkb
    exact hb k hkb

/-- The same decomposition as an equality of events (sets of increment sequences). -/
lemma cone_record_event_inter (a b : ℕ) (hab : a < b) :
    {z : ℕ → ℝ × ℝ | IsConeRecord z a} ∩
        {z | IsConeRecordAfter z a b} =
      {z | IsConeRecord z a} ∩ {z | IsConeRecord z b} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  exact cone_record_decomposition z hab

end Erdos521
