import ErdosProblems.Erdos686EvenK32TableP439S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_439_shard_2 :
    ∀ w : ZMod 439, 256 ≤ w.val → w.val < 384 → ∀ v : ZMod 439,
      evenTable32S w = 4 * evenTable32S v →
        even32A439 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
