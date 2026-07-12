import ErdosProblems.Erdos686EvenK32TableP7S0
namespace Erdos686.Erdos686Variant

theorem even32_allowed_7 : ∀ w v : ZMod 7,
    evenTable32S w = 4 * evenTable32S v →
      even32A7 (evenTable32T w - 2 * evenTable32T v) = true := by
  intro w v hS
  exact even32_allowed_7_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
