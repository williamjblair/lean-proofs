import ErdosProblems.Erdos686EvenK28TableP277
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_5_shard_0 :
    ∀ w : ZMod 5, 0 ≤ w.val → w.val < 5 → ∀ v : ZMod 5,
      evenTable28S w = 4 * evenTable28S v →
        even28A5 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
