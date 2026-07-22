import ErdosProblems.Erdos686.EvenK.K28.Core
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_29_shard_0 :
    ∀ w : ZMod 29, 0 ≤ w.val → w.val < 29 → ∀ v : ZMod 29,
      evenTable28S w = 4 * evenTable28S v →
        even28A29 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
