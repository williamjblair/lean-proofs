import ErdosProblems.Erdos686EvenK18TableP227S0
import ErdosProblems.Erdos686EvenK18TableP227S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_227 : ∀ w v : ZMod 227,
    evenTable18S w = 4 * evenTable18S v →
      even18A227 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_227_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_227_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
