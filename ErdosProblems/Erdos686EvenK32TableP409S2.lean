import ErdosProblems.Erdos686EvenK32TableP409S1
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_409_shard_2 :
    ∀ w : ZMod 409, 256 ≤ w.val → w.val < 384 → ∀ v : ZMod 409,
      evenTable32S w = 4 * evenTable32S v →
        even32A409 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
