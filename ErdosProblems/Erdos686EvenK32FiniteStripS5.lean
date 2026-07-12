import ErdosProblems.Erdos686EvenK32FiniteStripS4
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_finite_strip_shard_5 :
    ∀ d : Fin 128, 72 ≤ d.val → d.val < 80 → ∀ a : Fin 222,
      evenTable32S
          (2 * (((22 * d.val - 31 + a.val) + d.val : ℕ) : ℤ) + 33) ≠
        4 * evenTable32S (2 * ((22 * d.val - 31 + a.val : ℕ) : ℤ) + 33) := by decide

end Erdos686.Erdos686Variant
