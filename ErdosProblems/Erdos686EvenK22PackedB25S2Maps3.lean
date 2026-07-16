import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (32000000 + (r.val : ZMod 257)) + 25))) = true →
      (215300914200198214168061353391840113095417514624264354738134630009660285894655).testBit r.val = true := by decide

theorem even22_b25_s2_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (32000000 + (i : ZMod 257)) + 25))) = true) :
    (215300914200198214168061353391840113095417514624264354738134630009660285894655).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_257_fin r
  change even22A257
    (-(33 * (46 * (32000000 + ((i % 257 : ℕ) : ZMod 257)) + 25))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (32000000 + (r.val : ZMod 263)) + 25))) = true →
      (14474011154448844854596613804222800061042016906439259011789202053149816107560895).testBit r.val = true := by decide

theorem even22_b25_s2_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (32000000 + (i : ZMod 263)) + 25))) = true) :
    (14474011154448844854596613804222800061042016906439259011789202053149816107560895).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_263_fin r
  change even22A263
    (-(33 * (46 * (32000000 + ((i % 263 : ℕ) : ZMod 263)) + 25))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (32000000 + (r.val : ZMod 269)) + 25))) = true →
      (829997243309162566995852226423779211261797708636841911411093674117994898180257791).testBit r.val = true := by decide

theorem even22_b25_s2_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (32000000 + (i : ZMod 269)) + 25))) = true) :
    (829997243309162566995852226423779211261797708636841911411093674117994898180257791).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_269_fin r
  change even22A269
    (-(33 * (46 * (32000000 + ((i % 269 : ℕ) : ZMod 269)) + 25))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (32000000 + (r.val : ZMod 271)) + 25))) = true →
      (3779451926915500212651498633619677141127297070856047651215876416814615195342077935).testBit r.val = true := by decide

theorem even22_b25_s2_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (32000000 + (i : ZMod 271)) + 25))) = true) :
    (3779451926915500212651498633619677141127297070856047651215876416814615195342077935).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_271_fin r
  change even22A271
    (-(33 * (46 * (32000000 + ((i % 271 : ℕ) : ZMod 271)) + 25))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (32000000 + (r.val : ZMod 277)) + 25))) = true →
      (227654649847761663269478471157006372988911759099309295592971276283477301458370555839).testBit r.val = true := by decide

theorem even22_b25_s2_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (32000000 + (i : ZMod 277)) + 25))) = true) :
    (227654649847761663269478471157006372988911759099309295592971276283477301458370555839).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_277_fin r
  change even22A277
    (-(33 * (46 * (32000000 + ((i % 277 : ℕ) : ZMod 277)) + 25))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (32000000 + (r.val : ZMod 281)) + 25))) = true →
      (3885189107352338321718435478031994750397329435405818228426893272023463069104878911471).testBit r.val = true := by decide

theorem even22_b25_s2_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (32000000 + (i : ZMod 281)) + 25))) = true) :
    (3885189107352338321718435478031994750397329435405818228426893272023463069104878911471).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_281_fin r
  change even22A281
    (-(33 * (46 * (32000000 + ((i % 281 : ℕ) : ZMod 281)) + 25))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (32000000 + (r.val : ZMod 283)) + 25))) = true →
      (15541113991988516541123693943879247753715289274936249293429413141970799703984137306111).testBit r.val = true := by decide

theorem even22_b25_s2_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (32000000 + (i : ZMod 283)) + 25))) = true) :
    (15541113991988516541123693943879247753715289274936249293429413141970799703984137306111).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_283_fin r
  change even22A283
    (-(33 * (46 * (32000000 + ((i % 283 : ℕ) : ZMod 283)) + 25))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (32000000 + (r.val : ZMod 293)) + 25))) = true →
      (7957171782542082212263454229790936106187640211616582776745944203298967845043556283580031).testBit r.val = true := by decide

theorem even22_b25_s2_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (32000000 + (i : ZMod 293)) + 25))) = true) :
    (7957171782542082212263454229790936106187640211616582776745944203298967845043556283580031).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_293_fin r
  change even22A293
    (-(33 * (46 * (32000000 + ((i % 293 : ℕ) : ZMod 293)) + 25))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 215300914200198214168061353391840113095417514624264354738134630009660285894655) (.leaf 263 14474011154448844854596613804222800061042016906439259011789202053149816107560895)) (.node (.leaf 269 829997243309162566995852226423779211261797708636841911411093674117994898180257791) (.leaf 271 3779451926915500212651498633619677141127297070856047651215876416814615195342077935))) (.node (.node (.leaf 277 227654649847761663269478471157006372988911759099309295592971276283477301458370555839) (.leaf 281 3885189107352338321718435478031994750397329435405818228426893272023463069104878911471)) (.node (.leaf 283 15541113991988516541123693943879247753715289274936249293429413141970799703984137306111) (.leaf 293 7957171782542082212263454229790936106187640211616582776745944203298967845043556283580031))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
