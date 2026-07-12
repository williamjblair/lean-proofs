import ErdosProblems.Erdos686EvenK18TableP307S0
import ErdosProblems.Erdos686EvenK18TableP307S1
import ErdosProblems.Erdos686EvenK18TableP307S2
namespace Erdos686.Erdos686Variant

theorem even18_allowed_307 : ∀ w v : ZMod 307,
    evenTable18S w = 4 * evenTable18S v →
      even18A307 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_307_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even18_allowed_307_shard_1 w (by omega) h1 v hS
  · exact even18_allowed_307_shard_2 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
