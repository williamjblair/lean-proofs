import ErdosProblems.Erdos686.EvenK.K18.Table.TableP313S0
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP313S1
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP313S2
namespace Erdos686.Erdos686Variant

theorem even18_allowed_313 : ∀ w v : ZMod 313,
    evenTable18S w = 4 * evenTable18S v →
      even18A313 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_313_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even18_allowed_313_shard_1 w (by omega) h1 v hS
  · exact even18_allowed_313_shard_2 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
