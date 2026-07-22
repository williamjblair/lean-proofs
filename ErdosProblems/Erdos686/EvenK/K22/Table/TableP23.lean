import ErdosProblems.Erdos686.EvenK.K22.Table.TableP23S0

namespace Erdos686.Erdos686Variant

theorem even22_allowed_23 : ∀ w v : ZMod 23,
    evenTable22S w = 4 * evenTable22S v →
      even22A23 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  exact even22_allowed_23_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
