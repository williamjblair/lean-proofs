import ErdosProblems.Erdos686.EvenK.K18.Table.TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
-- Exhaustive shard: only centers with w.val in [256, 313) reach the inner loop.
set_option maxRecDepth 1000000 in
theorem even18_allowed_313_shard_2 :
    ∀ w : ZMod 313, 256 ≤ w.val → w.val < 313 → ∀ v : ZMod 313,
      evenTable18S w = 4 * evenTable18S v →
        even18A313 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
