import ErdosProblems.Erdos686.EvenK.K22.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_829_shard_6 :
    ∀ w : ZMod 829, 768 ≤ w.val → w.val < 829 → ∀ v : ZMod 829,
      evenTable22S w = 4 * evenTable22S v →
        even22A829 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
