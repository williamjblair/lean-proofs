import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (48000000 + (r.val : ZMod 257)) + 25))) = true →
      (231584178474632390847141970017375458894233975016265492221177694737350545899519).testBit r.val = true := by decide

theorem even22_b25_s3_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (48000000 + (i : ZMod 257)) + 25))) = true) :
    (231584178474632390847141970017375458894233975016265492221177694737350545899519).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_257_fin r
  change even22A257
    (-(33 * (46 * (48000000 + ((i % 257 : ℕ) : ZMod 257)) + 25))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (48000000 + (r.val : ZMod 263)) + 25))) = true →
      (14589795293076569147206450314529073154614864159199144256284473605177084011339775).testBit r.val = true := by decide

theorem even22_b25_s3_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (48000000 + (i : ZMod 263)) + 25))) = true) :
    (14589795293076569147206450314529073154614864159199144256284473605177084011339775).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_263_fin r
  change even22A263
    (-(33 * (46 * (48000000 + ((i % 263 : ℕ) : ZMod 263)) + 25))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (48000000 + (r.val : ZMod 269)) + 25))) = true →
      (948568795032094272857664884198893308479638652512441868961945822353238887147370495).testBit r.val = true := by decide

theorem even22_b25_s3_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (48000000 + (i : ZMod 269)) + 25))) = true) :
    (948568795032094272857664884198893308479638652512441868961945822353238887147370495).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_269_fin r
  change even22A269
    (-(33 * (46 * (48000000 + ((i % 269 : ℕ) : ZMod 269)) + 25))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (48000000 + (r.val : ZMod 271)) + 25))) = true →
      (3794273314330973254322264736100102657463278179479798173147923428637701916791406591).testBit r.val = true := by decide

theorem even22_b25_s3_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (48000000 + (i : ZMod 271)) + 25))) = true) :
    (3794273314330973254322264736100102657463278179479798173147923428637701916791406591).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_271_fin r
  change even22A271
    (-(33 * (46 * (48000000 + ((i % 271 : ℕ) : ZMod 271)) + 25))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (48000000 + (r.val : ZMod 277)) + 25))) = true →
      (242573745129180490528678228056212435105399807962953461884571762309492947242715185151).testBit r.val = true := by decide

theorem even22_b25_s3_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (48000000 + (i : ZMod 277)) + 25))) = true) :
    (242573745129180490528678228056212435105399807962953461884571762309492947242715185151).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_277_fin r
  change even22A277
    (-(33 * (46 * (48000000 + ((i % 277 : ℕ) : ZMod 277)) + 25))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (48000000 + (r.val : ZMod 281)) + 25))) = true →
      (3885308141676585778471694676424544905773322456187696393108366752088953491029818865135).testBit r.val = true := by decide

theorem even22_b25_s3_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (48000000 + (i : ZMod 281)) + 25))) = true) :
    (3885308141676585778471694676424544905773322456187696393108366752088953491029818865135).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_281_fin r
  change even22A281
    (-(33 * (46 * (48000000 + ((i % 281 : ℕ) : ZMod 281)) + 25))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (48000000 + (r.val : ZMod 283)) + 25))) = true →
      (15541351137805390848849411147633216598924083711638505468377404667382053412292511334399).testBit r.val = true := by decide

theorem even22_b25_s3_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (48000000 + (i : ZMod 283)) + 25))) = true) :
    (15541351137805390848849411147633216598924083711638505468377404667382053412292511334399).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_283_fin r
  change even22A283
    (-(33 * (46 * (48000000 + ((i % 283 : ℕ) : ZMod 283)) + 25))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (48000000 + (r.val : ZMod 293)) + 25))) = true →
      (15914343565053467028652050093536532202548211435897388853771773597637931144314923595595743).testBit r.val = true := by decide

theorem even22_b25_s3_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (48000000 + (i : ZMod 293)) + 25))) = true) :
    (15914343565053467028652050093536532202548211435897388853771773597637931144314923595595743).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_293_fin r
  change even22A293
    (-(33 * (46 * (48000000 + ((i % 293 : ℕ) : ZMod 293)) + 25))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231584178474632390847141970017375458894233975016265492221177694737350545899519) (.leaf 263 14589795293076569147206450314529073154614864159199144256284473605177084011339775)) (.node (.leaf 269 948568795032094272857664884198893308479638652512441868961945822353238887147370495) (.leaf 271 3794273314330973254322264736100102657463278179479798173147923428637701916791406591))) (.node (.node (.leaf 277 242573745129180490528678228056212435105399807962953461884571762309492947242715185151) (.leaf 281 3885308141676585778471694676424544905773322456187696393108366752088953491029818865135)) (.node (.leaf 283 15541351137805390848849411147633216598924083711638505468377404667382053412292511334399) (.leaf 293 15914343565053467028652050093536532202548211435897388853771773597637931144314923595595743))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
