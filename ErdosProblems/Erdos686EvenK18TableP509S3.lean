import ErdosProblems.Erdos686EvenK18TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exhaustive shard: only centers with w.val in [384, 509) reach the inner loop.
set_option maxRecDepth 1000000 in
theorem even18_allowed_509_shard_3 :
    ∀ w : ZMod 509, 384 ≤ w.val → w.val < 509 → ∀ v : ZMod 509,
      evenTable18S w = 4 * evenTable18S v →
        even18A509 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
