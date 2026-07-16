import ErdosProblems.Erdos686EvenK22TableP173S0
import ErdosProblems.Erdos686EvenK22TableP173S1

namespace Erdos686.Erdos686Variant

theorem even22_allowed_173 : ∀ w v : ZMod 173,
    evenTable22S w = 4 * evenTable22S v →
      even22A173 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_173_shard_0 w (by omega) h0 v hS
  · exact even22_allowed_173_shard_1 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
