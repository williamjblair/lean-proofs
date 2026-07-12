import ErdosProblems.Erdos686EvenK28TableP37S0
namespace Erdos686.Erdos686Variant

theorem even28_allowed_37 : ∀ w v : ZMod 37,
    evenTable28S w = 4 * evenTable28S v →
      even28A37 (evenTable28T w - 2 * evenTable28T v) = true := by
  intro w v hS
  exact even28_allowed_37_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
