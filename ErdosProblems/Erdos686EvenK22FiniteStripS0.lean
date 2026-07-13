import ErdosProblems.Erdos686EvenK22Defs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_finite_strip_shard_0 :
    ∀ d : Fin 250, 27 ≤ d.val → d.val < 35 → ∀ a : Fin 120,
      5 * (15 * d.val - 21 + a.val + 1) < 77 * d.val →
      evenTable22S
          (2 * (((15 * d.val - 21 + a.val) + d.val : ℕ) : ℤ) + 23) ≠
        4 * evenTable22S (2 * ((15 * d.val - 21 + a.val : ℕ) : ℤ) + 23) := by decide

end Erdos686.Erdos686Variant
