import ErdosProblems.Erdos686.EvenK.K32.Table.TableP443S2
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_443_shard_3 :
    ∀ w : ZMod 443, 384 ≤ w.val → w.val < 443 → ∀ v : ZMod 443,
      evenTable32S w = 4 * evenTable32S v →
        even32A443 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
