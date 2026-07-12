import ErdosProblems.Erdos686EvenK28FiniteStripS44
namespace Erdos686.Erdos686Variant

theorem even28_finite_strip :
    ∀ d : Fin 384, 28 ≤ d.val → ∀ n : Fin 7564,
      19 * d.val < n.val + 28 → 4 * (n.val + 1) < 79 * d.val →
        evenTable28S (2 * ((n.val + d.val : ℕ) : ℤ) + 29) ≠
          4 * evenTable28S (2 * (n.val : ℤ) + 29) := by
  intro d hd n hlo hhi
  let base := 19 * d.val - 27
  let a := n.val - base
  have hbase : base ≤ n.val := by dsimp [base]; omega
  have hna : base + a = n.val := by dsimp [a]; omega
  have halt : a < 314 := by dsimp [a, base] at *; omega
  let fa : Fin 314 := ⟨a, halt⟩
  have hainequality : 4 * (base + a + 1) < 79 * d.val := by rw [hna]; exact hhi
  by_cases h0 : d.val < 36
  · have h := even28_finite_strip_shard_0 d (by omega) h0 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h1 : d.val < 44
  · have h := even28_finite_strip_shard_1 d (by omega) h1 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h2 : d.val < 52
  · have h := even28_finite_strip_shard_2 d (by omega) h2 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h3 : d.val < 60
  · have h := even28_finite_strip_shard_3 d (by omega) h3 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h4 : d.val < 68
  · have h := even28_finite_strip_shard_4 d (by omega) h4 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h5 : d.val < 76
  · have h := even28_finite_strip_shard_5 d (by omega) h5 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h6 : d.val < 84
  · have h := even28_finite_strip_shard_6 d (by omega) h6 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h7 : d.val < 92
  · have h := even28_finite_strip_shard_7 d (by omega) h7 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h8 : d.val < 100
  · have h := even28_finite_strip_shard_8 d (by omega) h8 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h9 : d.val < 108
  · have h := even28_finite_strip_shard_9 d (by omega) h9 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h10 : d.val < 116
  · have h := even28_finite_strip_shard_10 d (by omega) h10 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h11 : d.val < 124
  · have h := even28_finite_strip_shard_11 d (by omega) h11 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h12 : d.val < 132
  · have h := even28_finite_strip_shard_12 d (by omega) h12 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h13 : d.val < 140
  · have h := even28_finite_strip_shard_13 d (by omega) h13 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h14 : d.val < 148
  · have h := even28_finite_strip_shard_14 d (by omega) h14 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h15 : d.val < 156
  · have h := even28_finite_strip_shard_15 d (by omega) h15 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h16 : d.val < 164
  · have h := even28_finite_strip_shard_16 d (by omega) h16 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h17 : d.val < 172
  · have h := even28_finite_strip_shard_17 d (by omega) h17 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h18 : d.val < 180
  · have h := even28_finite_strip_shard_18 d (by omega) h18 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h19 : d.val < 188
  · have h := even28_finite_strip_shard_19 d (by omega) h19 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h20 : d.val < 196
  · have h := even28_finite_strip_shard_20 d (by omega) h20 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h21 : d.val < 204
  · have h := even28_finite_strip_shard_21 d (by omega) h21 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h22 : d.val < 212
  · have h := even28_finite_strip_shard_22 d (by omega) h22 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h23 : d.val < 220
  · have h := even28_finite_strip_shard_23 d (by omega) h23 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h24 : d.val < 228
  · have h := even28_finite_strip_shard_24 d (by omega) h24 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h25 : d.val < 236
  · have h := even28_finite_strip_shard_25 d (by omega) h25 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h26 : d.val < 244
  · have h := even28_finite_strip_shard_26 d (by omega) h26 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h27 : d.val < 252
  · have h := even28_finite_strip_shard_27 d (by omega) h27 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h28 : d.val < 260
  · have h := even28_finite_strip_shard_28 d (by omega) h28 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h29 : d.val < 268
  · have h := even28_finite_strip_shard_29 d (by omega) h29 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h30 : d.val < 276
  · have h := even28_finite_strip_shard_30 d (by omega) h30 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h31 : d.val < 284
  · have h := even28_finite_strip_shard_31 d (by omega) h31 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h32 : d.val < 292
  · have h := even28_finite_strip_shard_32 d (by omega) h32 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h33 : d.val < 300
  · have h := even28_finite_strip_shard_33 d (by omega) h33 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h34 : d.val < 308
  · have h := even28_finite_strip_shard_34 d (by omega) h34 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h35 : d.val < 316
  · have h := even28_finite_strip_shard_35 d (by omega) h35 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h36 : d.val < 324
  · have h := even28_finite_strip_shard_36 d (by omega) h36 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h37 : d.val < 332
  · have h := even28_finite_strip_shard_37 d (by omega) h37 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h38 : d.val < 340
  · have h := even28_finite_strip_shard_38 d (by omega) h38 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h39 : d.val < 348
  · have h := even28_finite_strip_shard_39 d (by omega) h39 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h40 : d.val < 356
  · have h := even28_finite_strip_shard_40 d (by omega) h40 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h41 : d.val < 364
  · have h := even28_finite_strip_shard_41 d (by omega) h41 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h42 : d.val < 372
  · have h := even28_finite_strip_shard_42 d (by omega) h42 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  by_cases h43 : d.val < 380
  · have h := even28_finite_strip_shard_43 d (by omega) h43 fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
  · have h := even28_finite_strip_shard_44 d (by omega) d.isLt fa
      (by dsimp [fa, base] at *; omega)
    dsimp [fa, base] at h
    rw [← hna]
    exact h
end Erdos686.Erdos686Variant
