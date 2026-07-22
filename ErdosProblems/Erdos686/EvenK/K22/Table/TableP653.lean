import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S0
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S1
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S2
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S3
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S4
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP653S5

namespace Erdos686.Erdos686Variant

theorem even22_allowed_653 : ∀ w v : ZMod 653,
    evenTable22S w = 4 * evenTable22S v →
      even22A653 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_653_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even22_allowed_653_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even22_allowed_653_shard_2 w (by omega) h2 v hS
  by_cases h3 : w.val < 512
  · exact even22_allowed_653_shard_3 w (by omega) h3 v hS
  by_cases h4 : w.val < 640
  · exact even22_allowed_653_shard_4 w (by omega) h4 v hS
  · exact even22_allowed_653_shard_5 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
