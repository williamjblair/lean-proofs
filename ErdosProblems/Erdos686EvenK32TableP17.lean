import ErdosProblems.Erdos686EvenK32TableP17S0
namespace Erdos686.Erdos686Variant

theorem even32_allowed_17 : ∀ w v : ZMod 17,
    evenTable32S w = 4 * evenTable32S v →
      even32A17 (evenTable32T w - 2 * evenTable32T v) = true := by
  intro w v hS
  exact even32_allowed_17_shard_0 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
