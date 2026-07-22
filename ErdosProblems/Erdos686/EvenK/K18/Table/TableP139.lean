import ErdosProblems.Erdos686.EvenK.K18.Table.TableP139S0
import ErdosProblems.Erdos686.EvenK.K18.Table.TableP139S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_139 : ∀ w v : ZMod 139,
    evenTable18S w = 4 * evenTable18S v →
      even18A139 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_139_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_139_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
