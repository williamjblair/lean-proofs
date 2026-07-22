import ErdosProblems.Erdos686.EvenK.K22.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_139_shard_1 :
    ∀ w : ZMod 139, 128 ≤ w.val → w.val < 139 → ∀ v : ZMod 139,
      evenTable22S w = 4 * evenTable22S v →
        even22A139 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
