import ErdosProblems.Erdos686EvenK32TableP443
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_7_shard_0 :
    ∀ w : ZMod 7, 0 ≤ w.val → w.val < 7 → ∀ v : ZMod 7,
      evenTable32S w = 4 * evenTable32S v →
        even32A7 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
