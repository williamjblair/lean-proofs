import ErdosProblems.Erdos686.EvenK.K32.FiniteStripS11
namespace Erdos686.Erdos686Variant

theorem even32_finite_strip :
    ∀ d : Fin 128, 32 ≤ d.val → ∀ n : Fin 2984,
      22 * d.val < n.val + 32 → 2 * n.val + 2 < 47 * d.val →
        evenTable32S (2 * ((n.val + d.val : ℕ) : ℤ) + 33) ≠
          4 * evenTable32S (2 * (n.val : ℤ) + 33) := by
  intro d hd n hlo hhi
  let base := 22 * d.val - 31
  let a := n.val - base
  have hbase : base ≤ n.val := by dsimp [base]; omega
  have hna : base + a = n.val := by dsimp [a]; omega
  have halt : a < 222 := by dsimp [a, base] at *; omega
  let fa : Fin 222 := ⟨a, halt⟩
  by_cases h0 : d.val < 40
  · have h := even32_finite_strip_shard_0 d (by omega) h0 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h1 : d.val < 48
  · have h := even32_finite_strip_shard_1 d (by omega) h1 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h2 : d.val < 56
  · have h := even32_finite_strip_shard_2 d (by omega) h2 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h3 : d.val < 64
  · have h := even32_finite_strip_shard_3 d (by omega) h3 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h4 : d.val < 72
  · have h := even32_finite_strip_shard_4 d (by omega) h4 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h5 : d.val < 80
  · have h := even32_finite_strip_shard_5 d (by omega) h5 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h6 : d.val < 88
  · have h := even32_finite_strip_shard_6 d (by omega) h6 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h7 : d.val < 96
  · have h := even32_finite_strip_shard_7 d (by omega) h7 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h8 : d.val < 104
  · have h := even32_finite_strip_shard_8 d (by omega) h8 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h9 : d.val < 112
  · have h := even32_finite_strip_shard_9 d (by omega) h9 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  by_cases h10 : d.val < 120
  · have h := even32_finite_strip_shard_10 d (by omega) h10 fa
    dsimp [fa] at h
    rw [← hna]
    exact h
  · have h := even32_finite_strip_shard_11 d (by omega) (by omega) fa
    dsimp [fa] at h
    rw [← hna]
    exact h
end Erdos686.Erdos686Variant
