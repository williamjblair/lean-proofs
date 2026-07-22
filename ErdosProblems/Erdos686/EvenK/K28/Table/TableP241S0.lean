import ErdosProblems.Erdos686.EvenK.K28.Table.TableP313
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_241_shard_0 :
    ∀ w : ZMod 241, 0 ≤ w.val → w.val < 128 → ∀ v : ZMod 241,
      evenTable28S w = 4 * evenTable28S v →
        even28A241 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
