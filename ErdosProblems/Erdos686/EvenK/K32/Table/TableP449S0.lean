import ErdosProblems.Erdos686.EvenK.K32.Table.TableP383
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_449_shard_0 :
    ∀ w : ZMod 449, 0 ≤ w.val → w.val < 128 → ∀ v : ZMod 449,
      evenTable32S w = 4 * evenTable32S v →
        even32A449 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
