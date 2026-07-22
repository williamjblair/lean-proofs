import ErdosProblems.Erdos686.EvenK.K18.Table.TableP97S0
namespace Erdos686.Erdos686Variant

theorem even18_allowed_97 : ∀ w v : ZMod 97,
    evenTable18S w = 4 * evenTable18S v →
      even18A97 (evenTable18T w - 2 * evenTable18T v) = true := by
  intro w v hS
  · exact even18_allowed_97_shard_0 w (by omega) (ZMod.val_lt w) v hS

end Erdos686.Erdos686Variant
