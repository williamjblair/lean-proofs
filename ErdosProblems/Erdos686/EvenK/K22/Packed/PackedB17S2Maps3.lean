import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s2_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (32000000 + (r.val : ZMod 257)) + 17))) = true →
      (231576227661998389784310387685039128351749382195193717545057365018752936050679).testBit r.val = true := by decide

theorem even22_b17_s2_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (32000000 + (i : ZMod 257)) + 17))) = true) :
    (231576227661998389784310387685039128351749382195193717545057365018752936050679).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_257_fin r
  change even22A257
    (-(33 * (46 * (32000000 + ((i % 257 : ℕ) : ZMod 257)) + 17))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (32000000 + (r.val : ZMod 263)) + 17))) = true →
      (14756254151324171723397975622676454282171914268333300308099490415145361304715007).testBit r.val = true := by decide

theorem even22_b17_s2_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (32000000 + (i : ZMod 263)) + 17))) = true) :
    (14756254151324171723397975622676454282171914268333300308099490415145361304715007).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_263_fin r
  change even22A263
    (-(33 * (46 * (32000000 + ((i % 263 : ℕ) : ZMod 263)) + 17))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (32000000 + (r.val : ZMod 269)) + 17))) = true →
      (948566985780696555041365172162785477057671880179195260811876049431129443153182205).testBit r.val = true := by decide

theorem even22_b17_s2_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (32000000 + (i : ZMod 269)) + 17))) = true) :
    (948566985780696555041365172162785477057671880179195260811876049431129443153182205).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_269_fin r
  change even22A269
    (-(33 * (46 * (32000000 + ((i % 269 : ℕ) : ZMod 269)) + 17))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (32000000 + (r.val : ZMod 271)) + 17))) = true →
      (3794036358060685915023983551698098859233848067902995852426042543671071480039342079).testBit r.val = true := by decide

theorem even22_b17_s2_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (32000000 + (i : ZMod 271)) + 17))) = true) :
    (3794036358060685915023983551698098859233848067902995852426042543671071480039342079).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_271_fin r
  change even22A271
    (-(33 * (46 * (32000000 + ((i % 271 : ℕ) : ZMod 271)) + 17))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (32000000 + (r.val : ZMod 277)) + 17))) = true →
      (182064996756169733950243411543798434160910682616147841428218651813605571760427104255).testBit r.val = true := by decide

theorem even22_b17_s2_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (32000000 + (i : ZMod 277)) + 17))) = true) :
    (182064996756169733950243411543798434160910682616147841428218651813605571760427104255).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_277_fin r
  change even22A277
    (-(33 * (46 * (32000000 + ((i % 277 : ℕ) : ZMod 277)) + 17))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (32000000 + (r.val : ZMod 281)) + 17))) = true →
      (3885337769975645631364722961873695681714312189237309071456488929337184557019066007547).testBit r.val = true := by decide

theorem even22_b17_s2_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (32000000 + (i : ZMod 281)) + 17))) = true) :
    (3885337769975645631364722961873695681714312189237309071456488929337184557019066007547).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_281_fin r
  change even22A281
    (-(33 * (46 * (32000000 + ((i % 281 : ℕ) : ZMod 281)) + 17))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (32000000 + (r.val : ZMod 283)) + 17))) = true →
      (5334750899641940187365837330845797369009012388673213732999110234958501686112822493151).testBit r.val = true := by decide

theorem even22_b17_s2_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (32000000 + (i : ZMod 283)) + 17))) = true) :
    (5334750899641940187365837330845797369009012388673213732999110234958501686112822493151).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_283_fin r
  change even22A283
    (-(33 * (46 * (32000000 + ((i % 283 : ℕ) : ZMod 283)) + 17))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (32000000 + (r.val : ZMod 293)) + 17))) = true →
      (11935256829511102464227631059170357995752532197586993161204330237503284548049800322220015).testBit r.val = true := by decide

theorem even22_b17_s2_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (32000000 + (i : ZMod 293)) + 17))) = true) :
    (11935256829511102464227631059170357995752532197586993161204330237503284548049800322220015).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_293_fin r
  change even22A293
    (-(33 * (46 * (32000000 + ((i % 293 : ℕ) : ZMod 293)) + 17))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB17S2Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231576227661998389784310387685039128351749382195193717545057365018752936050679) (.leaf 263 14756254151324171723397975622676454282171914268333300308099490415145361304715007)) (.node (.leaf 269 948566985780696555041365172162785477057671880179195260811876049431129443153182205) (.leaf 271 3794036358060685915023983551698098859233848067902995852426042543671071480039342079))) (.node (.node (.leaf 277 182064996756169733950243411543798434160910682616147841428218651813605571760427104255) (.leaf 281 3885337769975645631364722961873695681714312189237309071456488929337184557019066007547)) (.node (.leaf 283 5334750899641940187365837330845797369009012388673213732999110234958501686112822493151) (.leaf 293 11935256829511102464227631059170357995752532197586993161204330237503284548049800322220015))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S2Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S2Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
