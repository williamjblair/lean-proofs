import ErdosProblems.Erdos686.EvenK.K32.Table.TableP521S3
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_521_shard_4 :
    ∀ w : ZMod 521, 512 ≤ w.val → w.val < 521 → ∀ v : ZMod 521,
      evenTable32S w = 4 * evenTable32S v →
        even32A521 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
