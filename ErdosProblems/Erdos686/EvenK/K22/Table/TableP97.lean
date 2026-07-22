import ErdosProblems.Erdos686.EvenK.K22.Table.TableP97S0

namespace Erdos686.Erdos686Variant

theorem even22_allowed_97 : ∀ w v : ZMod 97,
    evenTable22S w = 4 * evenTable22S v →
      even22A97 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  exact even22_allowed_97_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
