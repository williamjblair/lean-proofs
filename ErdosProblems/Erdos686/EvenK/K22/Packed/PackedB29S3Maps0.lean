import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s3_map_83_fin : ∀ r : Fin 83,
    even22A83 (-(33 * (46 * (48000000 + (r.val : ZMod 83)) + 29))) = true →
      (9671406412801845321793279).testBit r.val = true := by decide

theorem even22_b29_s3_map_83 (i : ℕ)
    (h : even22A83 (-(33 * (46 * (48000000 + (i : ZMod 83)) + 29))) = true) :
    (9671406412801845321793279).testBit (i % 83) = true := by
  let r : Fin 83 := ⟨i % 83, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_83_fin r
  change even22A83
    (-(33 * (46 * (48000000 + ((i % 83 : ℕ) : ZMod 83)) + 29))) = true
  have hcast : (i : ZMod 83) = ((i % 83 : ℕ) : ZMod 83) :=
    (ZMod.natCast_mod i 83).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_97_fin : ∀ r : Fin 97,
    even22A97 (-(33 * (46 * (48000000 + (r.val : ZMod 97)) + 29))) = true →
      (158456306139062743708507013119).testBit r.val = true := by decide

theorem even22_b29_s3_map_97 (i : ℕ)
    (h : even22A97 (-(33 * (46 * (48000000 + (i : ZMod 97)) + 29))) = true) :
    (158456306139062743708507013119).testBit (i % 97) = true := by
  let r : Fin 97 := ⟨i % 97, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_97_fin r
  change even22A97
    (-(33 * (46 * (48000000 + ((i % 97 : ℕ) : ZMod 97)) + 29))) = true
  have hcast : (i : ZMod 97) = ((i % 97 : ℕ) : ZMod 97) :=
    (ZMod.natCast_mod i 97).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_101_fin : ∀ r : Fin 101,
    even22A101 (-(33 * (46 * (48000000 + (r.val : ZMod 101)) + 29))) = true →
      (2218388550251827500029554196479).testBit r.val = true := by decide

theorem even22_b29_s3_map_101 (i : ℕ)
    (h : even22A101 (-(33 * (46 * (48000000 + (i : ZMod 101)) + 29))) = true) :
    (2218388550251827500029554196479).testBit (i % 101) = true := by
  let r : Fin 101 := ⟨i % 101, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_101_fin r
  change even22A101
    (-(33 * (46 * (48000000 + ((i % 101 : ℕ) : ZMod 101)) + 29))) = true
  have hcast : (i : ZMod 101) = ((i % 101 : ℕ) : ZMod 101) :=
    (ZMod.natCast_mod i 101).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_127_fin : ∀ r : Fin 127,
    even22A127 (-(33 * (46 * (48000000 + (r.val : ZMod 127)) + 29))) = true →
      (126941273592198220695350707504336076539).testBit r.val = true := by decide

theorem even22_b29_s3_map_127 (i : ℕ)
    (h : even22A127 (-(33 * (46 * (48000000 + (i : ZMod 127)) + 29))) = true) :
    (126941273592198220695350707504336076539).testBit (i % 127) = true := by
  let r : Fin 127 := ⟨i % 127, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_127_fin r
  change even22A127
    (-(33 * (46 * (48000000 + ((i % 127 : ℕ) : ZMod 127)) + 29))) = true
  have hcast : (i : ZMod 127) = ((i % 127 : ℕ) : ZMod 127) :=
    (ZMod.natCast_mod i 127).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_131_fin : ∀ r : Fin 131,
    even22A131 (-(33 * (46 * (48000000 + (r.val : ZMod 131)) + 29))) = true →
      (1276058794784266742123840913282279407615).testBit r.val = true := by decide

theorem even22_b29_s3_map_131 (i : ℕ)
    (h : even22A131 (-(33 * (46 * (48000000 + (i : ZMod 131)) + 29))) = true) :
    (1276058794784266742123840913282279407615).testBit (i % 131) = true := by
  let r : Fin 131 := ⟨i % 131, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_131_fin r
  change even22A131
    (-(33 * (46 * (48000000 + ((i % 131 : ℕ) : ZMod 131)) + 29))) = true
  have hcast : (i : ZMod 131) = ((i % 131 : ℕ) : ZMod 131) :=
    (ZMod.natCast_mod i 131).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_139_fin : ∀ r : Fin 139,
    even22A139 (-(33 * (46 * (48000000 + (r.val : ZMod 139)) + 29))) = true →
      (696887653587015573438211272420345679708091).testBit r.val = true := by decide

theorem even22_b29_s3_map_139 (i : ℕ)
    (h : even22A139 (-(33 * (46 * (48000000 + (i : ZMod 139)) + 29))) = true) :
    (696887653587015573438211272420345679708091).testBit (i % 139) = true := by
  let r : Fin 139 := ⟨i % 139, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_139_fin r
  change even22A139
    (-(33 * (46 * (48000000 + ((i % 139 : ℕ) : ZMod 139)) + 29))) = true
  have hcast : (i : ZMod 139) = ((i % 139 : ℕ) : ZMod 139) :=
    (ZMod.natCast_mod i 139).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_149_fin : ∀ r : Fin 149,
    even22A149 (-(33 * (46 * (48000000 + (r.val : ZMod 149)) + 29))) = true →
      (713623845023751627831501496881849820902326271).testBit r.val = true := by decide

theorem even22_b29_s3_map_149 (i : ℕ)
    (h : even22A149 (-(33 * (46 * (48000000 + (i : ZMod 149)) + 29))) = true) :
    (713623845023751627831501496881849820902326271).testBit (i % 149) = true := by
  let r : Fin 149 := ⟨i % 149, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_149_fin r
  change even22A149
    (-(33 * (46 * (48000000 + ((i % 149 : ℕ) : ZMod 149)) + 29))) = true
  have hcast : (i : ZMod 149) = ((i % 149 : ℕ) : ZMod 149) :=
    (ZMod.natCast_mod i 149).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_151_fin : ∀ r : Fin 151,
    even22A151 (-(33 * (46 * (48000000 + (r.val : ZMod 151)) + 29))) = true →
      (2854484496376137727266533807570562724680171519).testBit r.val = true := by decide

theorem even22_b29_s3_map_151 (i : ℕ)
    (h : even22A151 (-(33 * (46 * (48000000 + (i : ZMod 151)) + 29))) = true) :
    (2854484496376137727266533807570562724680171519).testBit (i % 151) = true := by
  let r : Fin 151 := ⟨i % 151, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_151_fin r
  change even22A151
    (-(33 * (46 * (48000000 + ((i % 151 : ℕ) : ZMod 151)) + 29))) = true
  have hcast : (i : ZMod 151) = ((i % 151 : ℕ) : ZMod 151) :=
    (ZMod.natCast_mod i 151).symm
  rw [← hcast]
  exact h

def even22PackedB29S3Group0Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 83 9671406412801845321793279) (.leaf 97 158456306139062743708507013119)) (.node (.leaf 101 2218388550251827500029554196479) (.leaf 127 126941273592198220695350707504336076539))) (.node (.node (.leaf 131 1276058794784266742123840913282279407615) (.leaf 139 696887653587015573438211272420345679708091)) (.node (.leaf 149 713623845023751627831501496881849820902326271) (.leaf 151 2854484496376137727266533807570562724680171519))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S3Group0TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S3Group0Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_83 i
          have hA := even22_allowed_int even22A83 even22_allowed_83 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_97 i
          have hA := even22_allowed_int even22A97 even22_allowed_97 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_101 i
          have hA := even22_allowed_int even22A101 even22_allowed_101 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_127 i
          have hA := even22_allowed_int even22A127 even22_allowed_127 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_131 i
          have hA := even22_allowed_int even22A131 even22_allowed_131 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_139 i
          have hA := even22_allowed_int even22A139 even22_allowed_139 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_149 i
          have hA := even22_allowed_int even22A149 even22_allowed_149 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_151 i
          have hA := even22_allowed_int even22A151 even22_allowed_151 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
