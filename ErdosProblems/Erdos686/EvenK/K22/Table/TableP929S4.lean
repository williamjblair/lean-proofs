import ErdosProblems.Erdos686.EvenK.K22.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_929_shard_4 :
    ∀ w : ZMod 929, 512 ≤ w.val → w.val < 640 → ∀ v : ZMod 929,
      evenTable22S w = 4 * evenTable22S v →
        even22A929 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
