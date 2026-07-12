import ErdosProblems.Erdos686EvenK18TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exhaustive shard: only centers with w.val in [256, 383) reach the inner loop.
set_option maxRecDepth 1000000 in
theorem even18_allowed_383_shard_2 :
    ∀ w : ZMod 383, 256 ≤ w.val → w.val < 383 → ∀ v : ZMod 383,
      evenTable18S w = 4 * evenTable18S v →
        even18A383 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
