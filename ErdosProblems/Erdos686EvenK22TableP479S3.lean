import ErdosProblems.Erdos686EvenK22TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_479_shard_3 :
    ∀ w : ZMod 479, 384 ≤ w.val → w.val < 479 → ∀ v : ZMod 479,
      evenTable22S w = 4 * evenTable22S v →
        even22A479 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
