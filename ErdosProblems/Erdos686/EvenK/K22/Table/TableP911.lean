import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S0
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S1
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S2
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S3
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S4
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S5
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S6
import ErdosProblems.Erdos686.EvenK.K22.Table.TableP911S7

namespace Erdos686.Erdos686Variant

theorem even22_allowed_911 : ∀ w v : ZMod 911,
    evenTable22S w = 4 * evenTable22S v →
      even22A911 (evenTable22T w - 2 * evenTable22T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even22_allowed_911_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even22_allowed_911_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even22_allowed_911_shard_2 w (by omega) h2 v hS
  by_cases h3 : w.val < 512
  · exact even22_allowed_911_shard_3 w (by omega) h3 v hS
  by_cases h4 : w.val < 640
  · exact even22_allowed_911_shard_4 w (by omega) h4 v hS
  by_cases h5 : w.val < 768
  · exact even22_allowed_911_shard_5 w (by omega) h5 v hS
  by_cases h6 : w.val < 896
  · exact even22_allowed_911_shard_6 w (by omega) h6 v hS
  · exact even22_allowed_911_shard_7 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
