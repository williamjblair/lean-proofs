import ErdosProblems.Erdos686EvenK32TableP383S0
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_383_shard_1 :
    ∀ w : ZMod 383, 128 ≤ w.val → w.val < 256 → ∀ v : ZMod 383,
      evenTable32S w = 4 * evenTable32S v →
        even32A383 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
