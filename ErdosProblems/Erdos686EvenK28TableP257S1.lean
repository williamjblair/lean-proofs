import ErdosProblems.Erdos686EvenK28TableP257S0
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_257_shard_1 :
    ∀ w : ZMod 257, 128 ≤ w.val → w.val < 256 → ∀ v : ZMod 257,
      evenTable28S w = 4 * evenTable28S v →
        even28A257 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
