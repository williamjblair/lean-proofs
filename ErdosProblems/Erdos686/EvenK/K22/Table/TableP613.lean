import ErdosProblems.Erdos686.EvenK.K22.Table.TableP613S0
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP613S1
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP613S2
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP613S3
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP613S4

namespace Erdos686.Erdos686Variant

theorem even22_allowed_613 : ∀ w v : ZMod 613,
    evenTable22S w = 4 * evenTable22S v →
      even22A613 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_613_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even22_allowed_613_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even22_allowed_613_shard_2 w (by omega) h2 v hS
  by_cases h3 : w.val < 512
  · exact even22_allowed_613_shard_3 w (by omega) h3 v hS
  · exact even22_allowed_613_shard_4 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
