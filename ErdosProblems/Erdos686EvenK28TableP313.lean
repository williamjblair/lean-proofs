import ErdosProblems.Erdos686EvenK28TableP313S2
namespace Erdos686.Erdos686Variant

theorem even28_allowed_313 : ∀ w v : ZMod 313,
    evenTable28S w = 4 * evenTable28S v →
      even28A313 (evenTable28T w - 2 * evenTable28T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even28_allowed_313_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even28_allowed_313_shard_1 w (by omega) h1 v hS
  · exact even28_allowed_313_shard_2 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
