import ErdosProblems.Erdos686EvenK32TableP457S2
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_457_shard_3 :
    ∀ w : ZMod 457, 384 ≤ w.val → w.val < 457 → ∀ v : ZMod 457,
      evenTable32S w = 4 * evenTable32S v →
        even32A457 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
