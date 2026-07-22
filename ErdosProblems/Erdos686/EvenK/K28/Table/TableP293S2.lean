import ErdosProblems.Erdos686.EvenK.K28.Table.TableP293S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_293_shard_2 :
    ∀ w : ZMod 293, 256 ≤ w.val → w.val < 293 → ∀ v : ZMod 293,
      evenTable28S w = 4 * evenTable28S v →
        even28A293 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
