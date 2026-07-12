import ErdosProblems.Erdos686EvenK28TableP5S0
namespace Erdos686.Erdos686Variant

theorem even28_allowed_5 : ∀ w v : ZMod 5,
    evenTable28S w = 4 * evenTable28S v →
      even28A5 (evenTable28T w - 2 * evenTable28T v) = true := by
  intro w v hS
  exact even28_allowed_5_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
