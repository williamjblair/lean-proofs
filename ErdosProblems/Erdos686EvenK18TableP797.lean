import ErdosProblems.Erdos686EvenK18TableP797S0
import ErdosProblems.Erdos686EvenK18TableP797S1
import ErdosProblems.Erdos686EvenK18TableP797S2
import ErdosProblems.Erdos686EvenK18TableP797S3
import ErdosProblems.Erdos686EvenK18TableP797S4
import ErdosProblems.Erdos686EvenK18TableP797S5
import ErdosProblems.Erdos686EvenK18TableP797S6
namespace Erdos686.Erdos686Variant

theorem even18_allowed_797 : ∀ w v : ZMod 797,
    evenTable18S w = 4 * evenTable18S v →
      even18A797 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even18_allowed_797_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even18_allowed_797_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even18_allowed_797_shard_2 w (by omega) h2 v hS
  by_cases h3 : w.val < 512
  · exact even18_allowed_797_shard_3 w (by omega) h3 v hS
  by_cases h4 : w.val < 640
  · exact even18_allowed_797_shard_4 w (by omega) h4 v hS
  by_cases h5 : w.val < 768
  · exact even18_allowed_797_shard_5 w (by omega) h5 v hS
  · exact even18_allowed_797_shard_6 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
