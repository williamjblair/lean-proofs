import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (48000000 + (r.val : ZMod 257)) + 21))) = true →
      (227513361111945995277903695279936694094796072268831078591362285880999835320319).testBit r.val = true := by decide

theorem even22_b21_s3_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (48000000 + (i : ZMod 257)) + 21))) = true) :
    (227513361111945995277903695279936694094796072268831078591362285880999835320319).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_257_fin r
  change even22A257
    (-(33 * (46 * (48000000 + ((i % 257 : ℕ) : ZMod 257)) + 21))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (48000000 + (r.val : ZMod 263)) + 21))) = true →
      (14821272576670223698822313300614363958278433530367142684752402295646910963122171).testBit r.val = true := by decide

theorem even22_b21_s3_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (48000000 + (i : ZMod 263)) + 21))) = true) :
    (14821272576670223698822313300614363958278433530367142684752402295646910963122171).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_263_fin r
  change even22A263
    (-(33 * (46 * (48000000 + ((i % 263 : ℕ) : ZMod 263)) + 21))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (48000000 + (r.val : ZMod 269)) + 21))) = true →
      (947638783276301004307099408050780239553885048834637922273386808103329235856260095).testBit r.val = true := by decide

theorem even22_b21_s3_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (48000000 + (i : ZMod 269)) + 21))) = true) :
    (947638783276301004307099408050780239553885048834637922273386808103329235856260095).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_269_fin r
  change even22A269
    (-(33 * (46 * (48000000 + ((i % 269 : ℕ) : ZMod 269)) + 21))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (48000000 + (r.val : ZMod 271)) + 21))) = true →
      (3794275180128377091639574036740734274967447428948677449259832885077019246562639615).testBit r.val = true := by decide

theorem even22_b21_s3_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (48000000 + (i : ZMod 271)) + 21))) = true) :
    (3794275180128377091639574036740734274967447428948677449259832885077019246562639615).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_271_fin r
  change even22A271
    (-(33 * (46 * (48000000 + ((i % 271 : ℕ) : ZMod 271)) + 21))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (48000000 + (r.val : ZMod 277)) + 21))) = true →
      (242833611512726889461353304419770599924058232452322577399510301757095676163231432701).testBit r.val = true := by decide

theorem even22_b21_s3_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (48000000 + (i : ZMod 277)) + 21))) = true) :
    (242833611512726889461353304419770599924058232452322577399510301757095676163231432701).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_277_fin r
  change even22A277
    (-(33 * (46 * (48000000 + ((i % 277 : ℕ) : ZMod 277)) + 21))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (48000000 + (r.val : ZMod 281)) + 21))) = true →
      (3869567741368776141235883387666123275790522257522195309140750203218904023004935610367).testBit r.val = true := by decide

theorem even22_b21_s3_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (48000000 + (i : ZMod 281)) + 21))) = true) :
    (3869567741368776141235883387666123275790522257522195309140750203218904023004935610367).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_281_fin r
  change even22A281
    (-(33 * (46 * (48000000 + ((i % 281 : ℕ) : ZMod 281)) + 21))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (48000000 + (r.val : ZMod 283)) + 21))) = true →
      (15480641808572929851963359713108855400604102717315195764232448477159982401313814085631).testBit r.val = true := by decide

theorem even22_b21_s3_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (48000000 + (i : ZMod 283)) + 21))) = true) :
    (15480641808572929851963359713108855400604102717315195764232448477159982401313814085631).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_283_fin r
  change even22A283
    (-(33 * (46 * (48000000 + ((i % 283 : ℕ) : ZMod 283)) + 21))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (48000000 + (r.val : ZMod 293)) + 21))) = true →
      (15914335976519333719647982076910247055697660940640907685661832858747986490891276140937215).testBit r.val = true := by decide

theorem even22_b21_s3_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (48000000 + (i : ZMod 293)) + 21))) = true) :
    (15914335976519333719647982076910247055697660940640907685661832858747986490891276140937215).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_293_fin r
  change even22A293
    (-(33 * (46 * (48000000 + ((i % 293 : ℕ) : ZMod 293)) + 21))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 227513361111945995277903695279936694094796072268831078591362285880999835320319) (.leaf 263 14821272576670223698822313300614363958278433530367142684752402295646910963122171)) (.node (.leaf 269 947638783276301004307099408050780239553885048834637922273386808103329235856260095) (.leaf 271 3794275180128377091639574036740734274967447428948677449259832885077019246562639615))) (.node (.node (.leaf 277 242833611512726889461353304419770599924058232452322577399510301757095676163231432701) (.leaf 281 3869567741368776141235883387666123275790522257522195309140750203218904023004935610367)) (.node (.leaf 283 15480641808572929851963359713108855400604102717315195764232448477159982401313814085631) (.leaf 293 15914335976519333719647982076910247055697660940640907685661832858747986490891276140937215))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
