import ErdosProblems.Erdos686.EvenK.K28.Table.TableP277S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_277_shard_2 :
    ∀ w : ZMod 277, 256 ≤ w.val → w.val < 277 → ∀ v : ZMod 277,
      evenTable28S w = 4 * evenTable28S v →
        even28A277 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
