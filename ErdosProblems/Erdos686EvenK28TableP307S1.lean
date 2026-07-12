import ErdosProblems.Erdos686EvenK28TableP307S0
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_307_shard_1 :
    ∀ w : ZMod 307, 128 ≤ w.val → w.val < 256 → ∀ v : ZMod 307,
      evenTable28S w = 4 * evenTable28S v →
        even28A307 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
