import ErdosProblems.Erdos686EvenK32TableP397
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_467_shard_0 :
    ∀ w : ZMod 467, 0 ≤ w.val → w.val < 128 → ∀ v : ZMod 467,
      evenTable32S w = 4 * evenTable32S v →
        even32A467 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
