import ErdosProblems.Erdos686.EvenK.K28.Table.TableP353S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even28_allowed_353_shard_2 :
    ∀ w : ZMod 353, 256 ≤ w.val → w.val < 353 → ∀ v : ZMod 353,
      evenTable28S w = 4 * evenTable28S v →
        even28A353 (evenTable28T w - 2 * evenTable28T v) = true := by decide

end Erdos686.Erdos686Variant
