import ErdosProblems.Erdos686EvenK18TableP211S0
import ErdosProblems.Erdos686EvenK18TableP211S1
namespace Erdos686.Erdos686Variant

theorem even18_allowed_211 : ∀ w v : ZMod 211,
    evenTable18S w = 4 * evenTable18S v →
      even18A211 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_211_shard_0 w (by omega) h0 v hS
  · exact even18_allowed_211_shard_1 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
