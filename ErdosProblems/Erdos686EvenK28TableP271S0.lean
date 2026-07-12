import ErdosProblems.Erdos686EvenK28TableP257
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_271_shard_0 :
    ∀ w : ZMod 271, 0 ≤ w.val → w.val < 128 → ∀ v : ZMod 271,
      evenTable28S w = 4 * evenTable28S v →
        even28A271 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
