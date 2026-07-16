import ErdosProblems.Erdos686EvenK22TableP499S0
import ErdosProblems.Erdos686EvenK22TableP499S1
import ErdosProblems.Erdos686EvenK22TableP499S2
import ErdosProblems.Erdos686EvenK22TableP499S3

namespace Erdos686.Erdos686Variant

theorem even22_allowed_499 : ∀ w v : ZMod 499,
    evenTable22S w = 4 * evenTable22S v →
      even22A499 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_499_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even22_allowed_499_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even22_allowed_499_shard_2 w (by omega) h2 v hS
  · exact even22_allowed_499_shard_3 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
