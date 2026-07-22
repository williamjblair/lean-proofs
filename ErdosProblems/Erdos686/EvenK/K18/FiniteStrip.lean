import ErdosProblems.Erdos686.EvenK.K18.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exactly 1,311 pairs reach the final equality test after the two ratio bounds.
set_option maxRecDepth 1000000 in
theorem even18_finite_strip :
    ∀ d : Fin 56, 18 ≤ d.val → ∀ n : Fin 687,
      12 * d.val < n.val + 18 → 2 * n.val + 2 < 25 * d.val →
        evenTable18S (2 * ((n.val + d.val : ℕ) : ℤ) + 19) ≠
          4 * evenTable18S (2 * (n.val : ℤ) + 19) := by decide

end Erdos686.Erdos686Variant
