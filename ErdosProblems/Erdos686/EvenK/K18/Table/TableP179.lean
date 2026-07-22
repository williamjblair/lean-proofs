import ErdosProblems.Erdos686.EvenK.K18.Table.TableP179S0
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP179S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_179 : ∀ w v : ZMod 179,
    evenTable18S w = 4 * evenTable18S v →
      even18A179 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_179_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_179_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
