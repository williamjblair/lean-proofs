import ErdosProblems.Erdos686EvenK18TableP241S0
import ErdosProblems.Erdos686EvenK18TableP241S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_241 : ∀ w v : ZMod 241,
    evenTable18S w = 4 * evenTable18S v →
      even18A241 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_241_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_241_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
