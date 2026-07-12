import ErdosProblems.Erdos686EvenK28TableP239S1
namespace Erdos686.Erdos686Variant

theorem even28_allowed_239 : ∀ w v : ZMod 239,
    evenTable28S w = 4 * evenTable28S v →
      even28A239 (evenTable28T w - 2 * evenTable28T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even28_allowed_239_shard_0 w (by omega) h0 v hS
  · exact even28_allowed_239_shard_1 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
