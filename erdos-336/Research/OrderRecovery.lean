import Mathlib
import Research.Basic
import Research.Normalization

/-!
# Recovering natural exact-order bounds from an integer translate
-/

namespace Erdos336

/-- The least eventual exact order is bounded by every eventual exact
representation length. -/
theorem HasExactOrder.le_of_eventuallyExactly
    {A : Set ℕ} {k q : ℕ} (hk : HasExactOrder A k)
    (hq : EventuallyExactly A q) : k ≤ q := by
  by_contra hnot
  have hqk : q < k := Nat.lt_of_not_ge hnot
  exact hk.2 q hqk hq

/-- If the normalized integer translate eventually covers at exact length
`q`, then the original set's exact order is at most `q`. -/
theorem exactOrder_le_of_translate_integer_cover
    {A : Set ℕ} {k q b : ℕ} (hk : HasExactOrder A k)
    (hD : EventuallyExactlyZ (TranslateNatSet A b) q) :
    k ≤ q := by
  apply hk.le_of_eventuallyExactly
  exact eventuallyExactly_of_eventuallyExactlyZ_translate hD

end Erdos336
