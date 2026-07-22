import ErdosProblems.Erdos686.EvenK.K22.Table.TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_577_shard_2 :
    ∀ w : ZMod 577, 256 ≤ w.val → w.val < 384 → ∀ v : ZMod 577,
      evenTable22S w = 4 * evenTable22S v →
        even22A577 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
