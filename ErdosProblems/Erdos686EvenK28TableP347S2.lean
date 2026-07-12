import ErdosProblems.Erdos686EvenK28TableP347S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_347_shard_2 :
    ∀ w : ZMod 347, 256 ≤ w.val → w.val < 347 → ∀ v : ZMod 347,
      evenTable28S w = 4 * evenTable28S v →
        even28A347 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
