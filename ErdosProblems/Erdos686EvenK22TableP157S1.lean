import ErdosProblems.Erdos686EvenK22TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_157_shard_1 :
    ∀ w : ZMod 157, 128 ≤ w.val → w.val < 157 → ∀ v : ZMod 157,
      evenTable22S w = 4 * evenTable22S v →
        even22A157 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
