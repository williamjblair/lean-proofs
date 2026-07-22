import ErdosProblems.Erdos686.EvenK.K32.FiniteStripS2
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_finite_strip_shard_3 :
    ∀ d : Fin 128, 56 ≤ d.val → d.val < 64 → ∀ a : Fin 222,
      evenTable32S
          (2 * (((22 * d.val - 31 + a.val) + d.val : ℕ) : ℤ) + 33) ≠
        4 * evenTable32S (2 * ((22 * d.val - 31 + a.val : ℕ) : ℤ) + 33) := by decide

end Erdos686.Erdos686Variant
