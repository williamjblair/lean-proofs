import ErdosProblems.Erdos686EvenK32TableP521S4
namespace Erdos686.Erdos686Variant

theorem even32_allowed_521 : ∀ w v : ZMod 521,
    evenTable32S w = 4 * evenTable32S v →
      even32A521 (evenTable32T w - 2 * evenTable32T v) = true := by
  intro w v hS
  by_cases h0 : w.val < 128
  · exact even32_allowed_521_shard_0 w (by omega) h0 v hS
  by_cases h1 : w.val < 256
  · exact even32_allowed_521_shard_1 w (by omega) h1 v hS
  by_cases h2 : w.val < 384
  · exact even32_allowed_521_shard_2 w (by omega) h2 v hS
  by_cases h3 : w.val < 512
  · exact even32_allowed_521_shard_3 w (by omega) h3 v hS
  · exact even32_allowed_521_shard_4 w (by omega) (ZMod.val_lt w) v hS
end Erdos686.Erdos686Variant
