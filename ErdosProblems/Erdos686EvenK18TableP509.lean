import ErdosProblems.Erdos686EvenK18TableP509S0
import ErdosProblems.Erdos686EvenK18TableP509S1
import ErdosProblems.Erdos686EvenK18TableP509S2
import ErdosProblems.Erdos686EvenK18TableP509S3
namespace Erdos686.Erdos686Variant

theorem even18_allowed_509 : ∀ w v : ZMod 509,
    evenTable18S w = 4 * evenTable18S v →
      even18A509 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_509_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even18_allowed_509_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even18_allowed_509_shard_2 w (by omega) h2 v hS
  · exact even18_allowed_509_shard_3 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
