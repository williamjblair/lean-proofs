import ErdosProblems.Erdos686.EvenK.K32.Table.TableP397S2
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_397_shard_3 :
    ∀ w : ZMod 397, 384 ≤ w.val → w.val < 397 → ∀ v : ZMod 397,
      evenTable32S w = 4 * evenTable32S v →
        even32A397 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
