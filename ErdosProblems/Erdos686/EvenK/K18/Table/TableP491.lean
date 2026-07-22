import ErdosProblems.Erdos686.EvenK.K18.Table.TableP491S0
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP491S1
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP491S2
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP491S3
namespace Erdos686.Erdos686Variant

theorem even18_allowed_491 : ∀ w v : ZMod 491,
    evenTable18S w = 4 * evenTable18S v →
      even18A491 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_491_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even18_allowed_491_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even18_allowed_491_shard_2 w (by omega) h2 v hS
  · exact even18_allowed_491_shard_3 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
