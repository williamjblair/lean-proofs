import ErdosProblems.Erdos686EvenK22TableP127S0

namespace Erdos686.Erdos686Variant

theorem even22_allowed_127 : ∀ w v : ZMod 127,
    evenTable22S w = 4 * evenTable22S v →
      even22A127 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  exact even22_allowed_127_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
