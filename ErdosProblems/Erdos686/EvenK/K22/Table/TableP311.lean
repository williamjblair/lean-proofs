import ErdosProblems.Erdos686.EvenK.K22.Table.TableP311S0
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP311S1
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP311S2

namespace Erdos686.Erdos686Variant

theorem even22_allowed_311 : ∀ w v : ZMod 311,
    evenTable22S w = 4 * evenTable22S v →
      even22A311 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_311_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even22_allowed_311_shard_1 w (by omega) h1 v hS
  · exact even22_allowed_311_shard_2 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
