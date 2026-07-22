import ErdosProblems.Erdos686.EvenK.K18.Table.TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exhaustive shard: only centers with w.val in [128, 256) reach the inner loop.
set_option maxRecDepth 1000000 in
theorem even18_allowed_373_shard_1 :
    ∀ w : ZMod 373, 128 ≤ w.val → w.val < 256 → ∀ v : ZMod 373,
      evenTable18S w = 4 * evenTable18S v →
        even18A373 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
