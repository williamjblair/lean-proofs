import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s1_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (16000000 + (r.val : ZMod 257)) + 25))) = true →
      (231555908914855921106193115655790483705497443085540686051928952501913157369343).testBit r.val = true := by decide

theorem even22_b25_s1_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (16000000 + (i : ZMod 257)) + 25))) = true) :
    (231555908914855921106193115655790483705497443085540686051928952501913157369343).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_257_fin r
  change even22A257
    (-(33 * (46 * (16000000 + ((i % 257 : ℕ) : ZMod 257)) + 25))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (16000000 + (r.val : ZMod 263)) + 25))) = true →
      (14358203163776665280195814547946094104011170281196296315518376457341287428767743).testBit r.val = true := by decide

theorem even22_b25_s1_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (16000000 + (i : ZMod 263)) + 25))) = true) :
    (14358203163776665280195814547946094104011170281196296315518376457341287428767743).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_263_fin r
  change even22A263
    (-(33 * (46 * (16000000 + ((i % 263 : ℕ) : ZMod 263)) + 25))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (16000000 + (r.val : ZMod 269)) + 25))) = true →
      (948568795004054243377783208842465179522309409258476735214014550748664058053918719).testBit r.val = true := by decide

theorem even22_b25_s1_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (16000000 + (i : ZMod 269)) + 25))) = true) :
    (948568795004054243377783208842465179522309409258476735214014550748664058053918719).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_269_fin r
  change even22A269
    (-(33 * (46 * (16000000 + ((i % 269 : ℕ) : ZMod 269)) + 25))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (16000000 + (r.val : ZMod 271)) + 25))) = true →
      (2845706385096282818729680527573490633666056401513314696605989747442052880490560511).testBit r.val = true := by decide

theorem even22_b25_s1_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (16000000 + (i : ZMod 271)) + 25))) = true) :
    (2845706385096282818729680527573490633666056401513314696605989747442052880490560511).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_271_fin r
  change even22A271
    (-(33 * (46 * (16000000 + ((i % 271 : ℕ) : ZMod 271)) + 25))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (16000000 + (r.val : ZMod 277)) + 25))) = true →
      (104335155854296257538485925748493728021277382637347076065461242235018210927873753069).testBit r.val = true := by decide

theorem even22_b25_s1_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (16000000 + (i : ZMod 277)) + 25))) = true) :
    (104335155854296257538485925748493728021277382637347076065461242235018210927873753069).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_277_fin r
  change even22A277
    (-(33 * (46 * (16000000 + ((i % 277 : ℕ) : ZMod 277)) + 25))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (16000000 + (r.val : ZMod 281)) + 25))) = true →
      (3885278498901713415104465539202051998261831234271113743713108684700098411649220733919).testBit r.val = true := by decide

theorem even22_b25_s1_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (16000000 + (i : ZMod 281)) + 25))) = true) :
    (3885278498901713415104465539202051998261831234271113743713108684700098411649220733919).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_281_fin r
  change even22A281
    (-(33 * (46 * (16000000 + ((i % 281 : ℕ) : ZMod 281)) + 25))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (16000000 + (r.val : ZMod 283)) + 25))) = true →
      (13598652602790833877945736452467481170837026850849954289391686837359136170724181401599).testBit r.val = true := by decide

theorem even22_b25_s1_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (16000000 + (i : ZMod 283)) + 25))) = true) :
    (13598652602790833877945736452467481170837026850849954289391686837359136170724181401599).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_283_fin r
  change even22A283
    (-(33 * (46 * (16000000 + ((i % 283 : ℕ) : ZMod 283)) + 25))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (16000000 + (r.val : ZMod 293)) + 25))) = true →
      (15914343563202595898726412831522757101890264357747507619756490046399575581644446530272255).testBit r.val = true := by decide

theorem even22_b25_s1_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (16000000 + (i : ZMod 293)) + 25))) = true) :
    (15914343563202595898726412831522757101890264357747507619756490046399575581644446530272255).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_293_fin r
  change even22A293
    (-(33 * (46 * (16000000 + ((i % 293 : ℕ) : ZMod 293)) + 25))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB25S1Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231555908914855921106193115655790483705497443085540686051928952501913157369343) (.leaf 263 14358203163776665280195814547946094104011170281196296315518376457341287428767743)) (.node (.leaf 269 948568795004054243377783208842465179522309409258476735214014550748664058053918719) (.leaf 271 2845706385096282818729680527573490633666056401513314696605989747442052880490560511))) (.node (.node (.leaf 277 104335155854296257538485925748493728021277382637347076065461242235018210927873753069) (.leaf 281 3885278498901713415104465539202051998261831234271113743713108684700098411649220733919)) (.node (.leaf 283 13598652602790833877945736452467481170837026850849954289391686837359136170724181401599) (.leaf 293 15914343563202595898726412831522757101890264357747507619756490046399575581644446530272255))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S1Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S1Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
