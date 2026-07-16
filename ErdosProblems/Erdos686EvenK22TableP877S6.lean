import ErdosProblems.Erdos686EvenK22TableDefs

namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem even22_allowed_877_shard_6 :
    ∀ w : ZMod 877, 768 ≤ w.val → w.val < 877 → ∀ v : ZMod 877,
      evenTable22S w = 4 * evenTable22S v →
        even22A877 (evenTable22T w - 2 * evenTable22T v) = true := by
  decide +kernel

end Erdos686.Erdos686Variant
