import ErdosProblems.Erdos686EvenK18TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exhaustive shard: only centers with w.val in [640, 768) reach the inner loop.
set_option maxRecDepth 1000000 in
theorem even18_allowed_797_shard_5 :
    ∀ w : ZMod 797, 640 ≤ w.val → w.val < 768 → ∀ v : ZMod 797,
      evenTable18S w = 4 * evenTable18S v →
        even18A797 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
