import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (0 + (r.val : ZMod 257)) + 25))) = true →
      (231583681548684797292995334485791655657515098250096746969358581970643785351165).testBit r.val = true := by decide

theorem even22_b25_s0_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (0 + (i : ZMod 257)) + 25))) = true) :
    (231583681548684797292995334485791655657515098250096746969358581970643785351165).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_257_fin r
  change even22A257
    (-(33 * (46 * (0 + ((i % 257 : ℕ) : ZMod 257)) + 25))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (0 + (r.val : ZMod 263)) + 25))) = true →
      (14126634886521216694976141527333547916865475775676525826527833353286751621209983).testBit r.val = true := by decide

theorem even22_b25_s0_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (0 + (i : ZMod 263)) + 25))) = true) :
    (14126634886521216694976141527333547916865475775676525826527833353286751621209983).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_263_fin r
  change even22A263
    (-(33 * (46 * (0 + ((i % 263 : ℕ) : ZMod 263)) + 25))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (0 + (r.val : ZMod 269)) + 25))) = true →
      (931887497176329928520445233037787966915790634850809001532675552830012245302836991).testBit r.val = true := by decide

theorem even22_b25_s0_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (0 + (i : ZMod 269)) + 25))) = true) :
    (931887497176329928520445233037787966915790634850809001532675552830012245302836991).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_269_fin r
  change even22A269
    (-(33 * (46 * (0 + ((i % 269 : ℕ) : ZMod 269)) + 25))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (0 + (r.val : ZMod 271)) + 25))) = true →
      (3794275176594682962082804973017770631403419041951156916822174068289064785523245055).testBit r.val = true := by decide

theorem even22_b25_s0_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (0 + (i : ZMod 271)) + 25))) = true) :
    (3794275176594682962082804973017770631403419041951156916822174068289064785523245055).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_271_fin r
  change even22A271
    (-(33 * (46 * (0 + ((i % 271 : ℕ) : ZMod 271)) + 25))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (0 + (r.val : ZMod 277)) + 25))) = true →
      (242326847449669017850426082114567330845956721898819240647916268505481528885347204511).testBit r.val = true := by decide

theorem even22_b25_s0_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (0 + (i : ZMod 277)) + 25))) = true) :
    (242326847449669017850426082114567330845956721898819240647916268505481528885347204511).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_277_fin r
  change even22A277
    (-(33 * (46 * (0 + ((i % 277 : ℕ) : ZMod 277)) + 25))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (0 + (r.val : ZMod 281)) + 25))) = true →
      (3885040430253218501597947142416951687509845192707357414350161724569117567799340826591).testBit r.val = true := by decide

theorem even22_b25_s0_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (0 + (i : ZMod 281)) + 25))) = true) :
    (3885040430253218501597947142416951687509845192707357414350161724569117567799340826591).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_281_fin r
  change even22A281
    (-(33 * (46 * (0 + ((i % 281 : ℕ) : ZMod 281)) + 25))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (0 + (r.val : ZMod 283)) + 25))) = true →
      (15533606847085496408076285890176674153621667639768173731967052388172218897278751996927).testBit r.val = true := by decide

theorem even22_b25_s0_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (0 + (i : ZMod 283)) + 25))) = true) :
    (15533606847085496408076285890176674153621667639768173731967052388172218897278751996927).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_283_fin r
  change even22A283
    (-(33 * (46 * (0 + ((i % 283 : ℕ) : ZMod 283)) + 25))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (0 + (r.val : ZMod 293)) + 25))) = true →
      (15914343564649042557847056242835952149785534389003744484447505596850412475377780818694127).testBit r.val = true := by decide

theorem even22_b25_s0_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (0 + (i : ZMod 293)) + 25))) = true) :
    (15914343564649042557847056242835952149785534389003744484447505596850412475377780818694127).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_293_fin r
  change even22A293
    (-(33 * (46 * (0 + ((i % 293 : ℕ) : ZMod 293)) + 25))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231583681548684797292995334485791655657515098250096746969358581970643785351165) (.leaf 263 14126634886521216694976141527333547916865475775676525826527833353286751621209983)) (.node (.leaf 269 931887497176329928520445233037787966915790634850809001532675552830012245302836991) (.leaf 271 3794275176594682962082804973017770631403419041951156916822174068289064785523245055))) (.node (.node (.leaf 277 242326847449669017850426082114567330845956721898819240647916268505481528885347204511) (.leaf 281 3885040430253218501597947142416951687509845192707357414350161724569117567799340826591)) (.node (.leaf 283 15533606847085496408076285890176674153621667639768173731967052388172218897278751996927) (.leaf 293 15914343564649042557847056242835952149785534389003744484447505596850412475377780818694127))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
