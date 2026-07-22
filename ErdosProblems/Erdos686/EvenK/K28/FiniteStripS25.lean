import ErdosProblems.Erdos686.EvenK.K28.FiniteStripS24
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_finite_strip_shard_25 :
    ∀ d : Fin 384, 228 ≤ d.val → d.val < 236 → ∀ a : Fin 314,
      4 * (19 * d.val - 27 + a.val + 1) < 79 * d.val →
      evenTable28S
          (2 * (((19 * d.val - 27 + a.val) + d.val : ℕ) : ℤ) + 29) ≠
        4 * evenTable28S (2 * ((19 * d.val - 27 + a.val : ℕ) : ℤ) + 29) := by decide

end Erdos686.Erdos686Variant
