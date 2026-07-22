import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s3_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (48000000 + (r.val : ZMod 257)) + 17))) = true →
      (231584178474632390847141970017375815532315210544994499350469007140202003560447).testBit r.val = true := by decide

theorem even22_b17_s3_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (48000000 + (i : ZMod 257)) + 17))) = true) :
    (231584178474632390847141970017375815532315210544994499350469007140202003560447).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_257_fin r
  change even22A257
    (-(33 * (46 * (48000000 + ((i % 257 : ℕ) : ZMod 257)) + 17))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (48000000 + (r.val : ZMod 263)) + 17))) = true →
      (14821386759754061329048319536100574499201654946943920640934748869968503687348207).testBit r.val = true := by decide

theorem even22_b17_s3_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (48000000 + (i : ZMod 263)) + 17))) = true) :
    (14821386759754061329048319536100574499201654946943920640934748869968503687348207).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_263_fin r
  change even22A263
    (-(33 * (46 * (48000000 + ((i % 263 : ℕ) : ZMod 263)) + 17))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (48000000 + (r.val : ZMod 269)) + 17))) = true →
      (948568766762514169551280859340223922159163335916570440707792207407358981630291951).testBit r.val = true := by decide

theorem even22_b17_s3_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (48000000 + (i : ZMod 269)) + 17))) = true) :
    (948568766762514169551280859340223922159163335916570440707792207407358981630291951).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_269_fin r
  change even22A269
    (-(33 * (46 * (48000000 + ((i % 269 : ℕ) : ZMod 269)) + 17))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (48000000 + (r.val : ZMod 271)) + 17))) = true →
      (3794275180114570228528427871675468085264185244080946608324715166127303609792069631).testBit r.val = true := by decide

theorem even22_b17_s3_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (48000000 + (i : ZMod 271)) + 17))) = true) :
    (3794275180114570228528427871675468085264185244080946608324715166127303609792069631).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_271_fin r
  change even22A271
    (-(33 * (46 * (48000000 + ((i % 271 : ℕ) : ZMod 271)) + 17))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (48000000 + (r.val : ZMod 277)) + 17))) = true →
      (172402349549060823849093378888189754901842052113595135951280320864395126082388360701).testBit r.val = true := by decide

theorem even22_b17_s3_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (48000000 + (i : ZMod 277)) + 17))) = true) :
    (172402349549060823849093378888189754901842052113595135951280320864395126082388360701).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_277_fin r
  change even22A277
    (-(33 * (46 * (48000000 + ((i % 277 : ℕ) : ZMod 277)) + 17))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (48000000 + (r.val : ZMod 281)) + 17))) = true →
      (3763906157299913894933910480268738369463632513835424136825097142308800035538864177141).testBit r.val = true := by decide

theorem even22_b17_s3_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (48000000 + (i : ZMod 281)) + 17))) = true) :
    (3763906157299913894933910480268738369463632513835424136825097142308800035538864177141).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_281_fin r
  change even22A281
    (-(33 * (46 * (48000000 + ((i % 281 : ℕ) : ZMod 281)) + 17))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (48000000 + (r.val : ZMod 283)) + 17))) = true →
      (13598681300232115174151165060488703211108723167911772432156479904440672401785047998463).testBit r.val = true := by decide

theorem even22_b17_s3_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (48000000 + (i : ZMod 283)) + 17))) = true) :
    (13598681300232115174151165060488703211108723167911772432156479904440672401785047998463).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_283_fin r
  change even22A283
    (-(33 * (46 * (48000000 + ((i % 283 : ℕ) : ZMod 283)) + 17))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (48000000 + (r.val : ZMod 293)) + 17))) = true →
      (15385876918024892076573690977444766890914446883622104073788183966845770846866826558668731).testBit r.val = true := by decide

theorem even22_b17_s3_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (48000000 + (i : ZMod 293)) + 17))) = true) :
    (15385876918024892076573690977444766890914446883622104073788183966845770846866826558668731).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_293_fin r
  change even22A293
    (-(33 * (46 * (48000000 + ((i % 293 : ℕ) : ZMod 293)) + 17))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB17S3Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231584178474632390847141970017375815532315210544994499350469007140202003560447) (.leaf 263 14821386759754061329048319536100574499201654946943920640934748869968503687348207)) (.node (.leaf 269 948568766762514169551280859340223922159163335916570440707792207407358981630291951) (.leaf 271 3794275180114570228528427871675468085264185244080946608324715166127303609792069631))) (.node (.node (.leaf 277 172402349549060823849093378888189754901842052113595135951280320864395126082388360701) (.leaf 281 3763906157299913894933910480268738369463632513835424136825097142308800035538864177141)) (.node (.leaf 283 13598681300232115174151165060488703211108723167911772432156479904440672401785047998463) (.leaf 293 15385876918024892076573690977444766890914446883622104073788183966845770846866826558668731))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S3Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S3Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
