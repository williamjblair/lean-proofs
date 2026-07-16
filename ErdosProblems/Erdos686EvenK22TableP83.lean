import ErdosProblems.Erdos686EvenK22TableP83S0

namespace Erdos686.Erdos686Variant

theorem even22_allowed_83 : ∀ w v : ZMod 83,
    evenTable22S w = 4 * evenTable22S v →
      even22A83 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  exact even22_allowed_83_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
