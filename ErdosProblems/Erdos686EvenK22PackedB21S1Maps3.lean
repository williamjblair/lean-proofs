import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (16000000 + (r.val : ZMod 257)) + 21))) = true →
      (231584178474632390847141958044741557457104390598955914357940737627553747959807).testBit r.val = true := by decide

theorem even22_b21_s1_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (16000000 + (i : ZMod 257)) + 21))) = true) :
    (231584178474632390847141958044741557457104390598955914357940737627553747959807).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_257_fin r
  change even22A257
    (-(33 * (46 * (16000000 + ((i % 257 : ℕ) : ZMod 257)) + 21))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (16000000 + (r.val : ZMod 263)) + 21))) = true →
      (14821157730963974383427540520116675711338309023532293172454233838280941332332535).testBit r.val = true := by decide

theorem even22_b21_s1_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (16000000 + (i : ZMod 263)) + 21))) = true) :
    (14821157730963974383427540520116675711338309023532293172454233838280941332332535).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_263_fin r
  change even22A263
    (-(33 * (46 * (16000000 + ((i % 263 : ℕ) : ZMod 263)) + 21))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (16000000 + (r.val : ZMod 269)) + 21))) = true →
      (948568795032094272909077436925666996873763510289232412616716360914080835028121567).testBit r.val = true := by decide

theorem even22_b21_s1_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (16000000 + (i : ZMod 269)) + 21))) = true) :
    (948568795032094272909077436925666996873763510289232412616716360914080835028121567).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_269_fin r
  change even22A269
    (-(33 * (46 * (16000000 + ((i % 269 : ℕ) : ZMod 269)) + 21))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (16000000 + (r.val : ZMod 271)) + 21))) = true →
      (3794275180128363608374817058087840425786662023916832303817875574737465406824382463).testBit r.val = true := by decide

theorem even22_b21_s1_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (16000000 + (i : ZMod 271)) + 21))) = true) :
    (3794275180128363608374817058087840425786662023916832303817875574737465406824382463).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_271_fin r
  change even22A271
    (-(33 * (46 * (16000000 + ((i % 271 : ℕ) : ZMod 271)) + 21))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (16000000 + (r.val : ZMod 277)) + 21))) = true →
      (240936205150799908973494828802422096191217442705749400608051079308651059677505781759).testBit r.val = true := by decide

theorem even22_b21_s1_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (16000000 + (i : ZMod 277)) + 21))) = true) :
    (240936205150799908973494828802422096191217442705749400608051079308651059677505781759).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_277_fin r
  change even22A277
    (-(33 * (46 * (16000000 + ((i % 277 : ℕ) : ZMod 277)) + 21))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (16000000 + (r.val : ZMod 281)) + 21))) = true →
      (3853797698286094140632842961685208738296230836940111575777875586959999475599454224383).testBit r.val = true := by decide

theorem even22_b21_s1_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (16000000 + (i : ZMod 281)) + 21))) = true) :
    (3853797698286094140632842961685208738296230836940111575777875586959999475599454224383).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_281_fin r
  change even22A281
    (-(33 * (46 * (16000000 + ((i % 281 : ℕ) : ZMod 281)) + 21))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (16000000 + (r.val : ZMod 283)) + 21))) = true →
      (13558812713399775791826897965250013776636964114287852029868095504723295884735174934527).testBit r.val = true := by decide

theorem even22_b21_s1_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (16000000 + (i : ZMod 283)) + 21))) = true) :
    (13558812713399775791826897965250013776636964114287852029868095504723295884735174934527).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_283_fin r
  change even22A283
    (-(33 * (46 * (16000000 + ((i % 283 : ℕ) : ZMod 283)) + 21))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (16000000 + (r.val : ZMod 293)) + 21))) = true →
      (15914100730110330010596236299481632402672648509540110240238386401921346672087727981199359).testBit r.val = true := by decide

theorem even22_b21_s1_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (16000000 + (i : ZMod 293)) + 21))) = true) :
    (15914100730110330010596236299481632402672648509540110240238386401921346672087727981199359).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_293_fin r
  change even22A293
    (-(33 * (46 * (16000000 + ((i % 293 : ℕ) : ZMod 293)) + 21))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231584178474632390847141958044741557457104390598955914357940737627553747959807) (.leaf 263 14821157730963974383427540520116675711338309023532293172454233838280941332332535)) (.node (.leaf 269 948568795032094272909077436925666996873763510289232412616716360914080835028121567) (.leaf 271 3794275180128363608374817058087840425786662023916832303817875574737465406824382463))) (.node (.node (.leaf 277 240936205150799908973494828802422096191217442705749400608051079308651059677505781759) (.leaf 281 3853797698286094140632842961685208738296230836940111575777875586959999475599454224383)) (.node (.leaf 283 13558812713399775791826897965250013776636964114287852029868095504723295884735174934527) (.leaf 293 15914100730110330010596236299481632402672648509540110240238386401921346672087727981199359))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
