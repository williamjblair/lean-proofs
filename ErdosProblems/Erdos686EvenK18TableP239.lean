import ErdosProblems.Erdos686EvenK18TableP239S0
import ErdosProblems.Erdos686EvenK18TableP239S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_239 : ∀ w v : ZMod 239,
    evenTable18S w = 4 * evenTable18S v →
      even18A239 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_239_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_239_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
