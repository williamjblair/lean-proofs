import ErdosProblems.Erdos686EvenK22FiniteStripS27

namespace Erdos686.Erdos686Variant

theorem even22_finite_strip :
    ∀ d : Fin 250, 27 ≤ d.val → ∀ n : Fin 3834,
      15 * d.val < n.val + 22 → 5 * (n.val + 1) < 77 * d.val →
        evenTable22S (2 * ((n.val + d.val : ℕ) : ℤ) + 23) ≠
          4 * evenTable22S (2 * (n.val : ℤ) + 23) := by
  intro d hd n hlo hhi
  let base := 15 * d.val - 21
  let a := n.val - base
  have hbase : base ≤ n.val := by dsimp [base]; omega
  have hna : base + a = n.val := by dsimp [a]; omega
  have halt : a < 120 := by dsimp [a, base] at *; omega
  let fa : Fin 120 := ⟨a, halt⟩
  have hainequality : 5 * (base + a + 1) < 77 * d.val := by
    rw [hna]
    exact hhi
  by_cases h0 : d.val < 35
  · have h := even22_finite_strip_shard_0 d (by omega) h0 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h1 : d.val < 43
  · have h := even22_finite_strip_shard_1 d (by omega) h1 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h2 : d.val < 51
  · have h := even22_finite_strip_shard_2 d (by omega) h2 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h3 : d.val < 59
  · have h := even22_finite_strip_shard_3 d (by omega) h3 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h4 : d.val < 67
  · have h := even22_finite_strip_shard_4 d (by omega) h4 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h5 : d.val < 75
  · have h := even22_finite_strip_shard_5 d (by omega) h5 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h6 : d.val < 83
  · have h := even22_finite_strip_shard_6 d (by omega) h6 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h7 : d.val < 91
  · have h := even22_finite_strip_shard_7 d (by omega) h7 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h8 : d.val < 99
  · have h := even22_finite_strip_shard_8 d (by omega) h8 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h9 : d.val < 107
  · have h := even22_finite_strip_shard_9 d (by omega) h9 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h10 : d.val < 115
  · have h := even22_finite_strip_shard_10 d (by omega) h10 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h11 : d.val < 123
  · have h := even22_finite_strip_shard_11 d (by omega) h11 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h12 : d.val < 131
  · have h := even22_finite_strip_shard_12 d (by omega) h12 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h13 : d.val < 139
  · have h := even22_finite_strip_shard_13 d (by omega) h13 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h14 : d.val < 147
  · have h := even22_finite_strip_shard_14 d (by omega) h14 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h15 : d.val < 155
  · have h := even22_finite_strip_shard_15 d (by omega) h15 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h16 : d.val < 163
  · have h := even22_finite_strip_shard_16 d (by omega) h16 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h17 : d.val < 171
  · have h := even22_finite_strip_shard_17 d (by omega) h17 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h18 : d.val < 179
  · have h := even22_finite_strip_shard_18 d (by omega) h18 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h19 : d.val < 187
  · have h := even22_finite_strip_shard_19 d (by omega) h19 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h20 : d.val < 195
  · have h := even22_finite_strip_shard_20 d (by omega) h20 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h21 : d.val < 203
  · have h := even22_finite_strip_shard_21 d (by omega) h21 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h22 : d.val < 211
  · have h := even22_finite_strip_shard_22 d (by omega) h22 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h23 : d.val < 219
  · have h := even22_finite_strip_shard_23 d (by omega) h23 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h24 : d.val < 227
  · have h := even22_finite_strip_shard_24 d (by omega) h24 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h25 : d.val < 235
  · have h := even22_finite_strip_shard_25 d (by omega) h25 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h26 : d.val < 243
  · have h := even22_finite_strip_shard_26 d (by omega) h26 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  · have h := even22_finite_strip_shard_27 d (by omega) d.isLt fa (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
end Erdos686.Erdos686Variant
