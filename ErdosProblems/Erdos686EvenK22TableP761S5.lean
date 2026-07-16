import ErdosProblems.Erdos686EvenK22TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_761_shard_5 :
    ∀ w : ZMod 761, 640 ≤ w.val → w.val < 761 → ∀ v : ZMod 761,
      evenTable22S w = 4 * evenTable22S v →
        even22A761 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
