import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s5_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (80000000 + (r.val : ZMod 257)) + 25))) = true →
      (231471100141166762825841083646387940757452541399214783685051059880553594486783).testBit r.val = true := by decide

theorem even22_b25_s5_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (80000000 + (i : ZMod 257)) + 25))) = true) :
    (231471100141166762825841083646387940757452541399214783685051059880553594486783).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_257_fin r
  change even22A257
    (-(33 * (46 * (80000000 + ((i % 257 : ℕ) : ZMod 257)) + 25))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (80000000 + (r.val : ZMod 263)) + 25))) = true →
      (14705591357726521080711768197820562679916711098200568226667522179094982302625791).testBit r.val = true := by decide

theorem even22_b25_s5_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (80000000 + (i : ZMod 263)) + 25))) = true) :
    (14705591357726521080711768197820562679916711098200568226667522179094982302625791).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_263_fin r
  change even22A263
    (-(33 * (46 * (80000000 + ((i % 263 : ℕ) : ZMod 263)) + 25))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (80000000 + (r.val : ZMod 269)) + 25))) = true →
      (889048042661325082331071036206140840007417119418394486988854442465136540148236287).testBit r.val = true := by decide

theorem even22_b25_s5_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (80000000 + (i : ZMod 269)) + 25))) = true) :
    (889048042661325082331071036206140840007417119418394486988854442465136540148236287).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_269_fin r
  change even22A269
    (-(33 * (46 * (80000000 + ((i % 269 : ℕ) : ZMod 269)) + 25))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (80000000 + (r.val : ZMod 271)) + 25))) = true →
      (3794246232106067762587403822039191542835317687168832580696357714321457155128950783).testBit r.val = true := by decide

theorem even22_b25_s5_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (80000000 + (i : ZMod 271)) + 25))) = true) :
    (3794246232106067762587403822039191542835317687168832580696357714321457155128950783).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_271_fin r
  change even22A271
    (-(33 * (46 * (80000000 + ((i % 271 : ℕ) : ZMod 271)) + 25))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (80000000 + (r.val : ZMod 277)) + 25))) = true →
      (242358856725309521365599227987243445914914994160694240166412036378271180464008687599).testBit r.val = true := by decide

theorem even22_b25_s5_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (80000000 + (i : ZMod 277)) + 25))) = true) :
    (242358856725309521365599227987243445914914994160694240166412036378271180464008687599).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_277_fin r
  change even22A277
    (-(33 * (46 * (80000000 + ((i % 277 : ℕ) : ZMod 277)) + 25))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (80000000 + (r.val : ZMod 281)) + 25))) = true →
      (3885322963064021960155309245035791359529068067145987717805995785783381030720117930743).testBit r.val = true := by decide

theorem even22_b25_s5_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (80000000 + (i : ZMod 281)) + 25))) = true) :
    (3885322963064021960155309245035791359529068067145987717805995785783381030720117930743).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_281_fin r
  change even22A281
    (-(33 * (46 * (80000000 + ((i % 281 : ℕ) : ZMod 281)) + 25))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (80000000 + (r.val : ZMod 283)) + 25))) = true →
      (13537965505551012469928556300311446601160625703911472894053721971808491626465033453567).testBit r.val = true := by decide

theorem even22_b25_s5_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (80000000 + (i : ZMod 283)) + 25))) = true) :
    (13537965505551012469928556300311446601160625703911472894053721971808491626465033453567).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_283_fin r
  change even22A283
    (-(33 * (46 * (80000000 + ((i % 283 : ℕ) : ZMod 283)) + 25))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (80000000 + (r.val : ZMod 293)) + 25))) = true →
      (15914343565111306751462226257974462674443772282089572642334751208614129755648376003887102).testBit r.val = true := by decide

theorem even22_b25_s5_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (80000000 + (i : ZMod 293)) + 25))) = true) :
    (15914343565111306751462226257974462674443772282089572642334751208614129755648376003887102).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_293_fin r
  change even22A293
    (-(33 * (46 * (80000000 + ((i % 293 : ℕ) : ZMod 293)) + 25))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB25S5Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231471100141166762825841083646387940757452541399214783685051059880553594486783) (.leaf 263 14705591357726521080711768197820562679916711098200568226667522179094982302625791)) (.node (.leaf 269 889048042661325082331071036206140840007417119418394486988854442465136540148236287) (.leaf 271 3794246232106067762587403822039191542835317687168832580696357714321457155128950783))) (.node (.node (.leaf 277 242358856725309521365599227987243445914914994160694240166412036378271180464008687599) (.leaf 281 3885322963064021960155309245035791359529068067145987717805995785783381030720117930743)) (.node (.leaf 283 13537965505551012469928556300311446601160625703911472894053721971808491626465033453567) (.leaf 293 15914343565111306751462226257974462674443772282089572642334751208614129755648376003887102))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S5Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S5Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
