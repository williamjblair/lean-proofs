import ErdosProblems.Erdos686EvenK32TableP431S2
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even32_allowed_431_shard_3 :
    ∀ w : ZMod 431, 384 ≤ w.val → w.val < 431 → ∀ v : ZMod 431,
      evenTable32S w = 4 * evenTable32S v →
        even32A431 (evenTable32T w - 2 * evenTable32T v) = true := by decide

end Erdos686.Erdos686Variant
