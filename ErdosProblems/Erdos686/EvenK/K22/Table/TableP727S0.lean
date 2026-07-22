import ErdosProblems.Erdos686.EvenK.K22.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_727_shard_0 :
    ∀ w : ZMod 727, 0 ≤ w.val → w.val < 128 → ∀ v : ZMod 727,
      evenTable22S w = 4 * evenTable22S v →
        even22A727 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
