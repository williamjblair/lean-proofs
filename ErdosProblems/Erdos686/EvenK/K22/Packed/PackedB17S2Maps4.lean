import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s2_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (32000000 + (r.val : ZMod 307)) + 17))) = true →
      (260738553512049029764507597111165865969269178425648845815083455986377538350456340196816321983).testBit r.val = true := by decide

theorem even22_b17_s2_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (32000000 + (i : ZMod 307)) + 17))) = true) :
    (260738553512049029764507597111165865969269178425648845815083455986377538350456340196816321983).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_307_fin r
  change even22A307
    (-(33 * (46 * (32000000 + ((i % 307 : ℕ) : ZMod 307)) + 17))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (32000000 + (r.val : ZMod 311)) + 17))) = true →
      (4106631704956598627552114124703660736104130033656461855861155743299806371079449435565921923071).testBit r.val = true := by decide

theorem even22_b17_s2_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (32000000 + (i : ZMod 311)) + 17))) = true) :
    (4106631704956598627552114124703660736104130033656461855861155743299806371079449435565921923071).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_311_fin r
  change even22A311
    (-(33 * (46 * (32000000 + ((i % 311 : ℕ) : ZMod 311)) + 17))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (32000000 + (r.val : ZMod 313)) + 17))) = true →
      (16589580894491056543086036920719841251219180742735293186312280741539805039656025808265884467199).testBit r.val = true := by decide

theorem even22_b17_s2_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (32000000 + (i : ZMod 313)) + 17))) = true) :
    (16589580894491056543086036920719841251219180742735293186312280741539805039656025808265884467199).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_313_fin r
  change even22A313
    (-(33 * (46 * (32000000 + ((i % 313 : ℕ) : ZMod 313)) + 17))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (32000000 + (r.val : ZMod 317)) + 17))) = true →
      (183561380925074263576960708835989630582873997469675778879266139811409446803816751666543909607167).testBit r.val = true := by decide

theorem even22_b17_s2_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (32000000 + (i : ZMod 317)) + 17))) = true) :
    (183561380925074263576960708835989630582873997469675778879266139811409446803816751666543909607167).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_317_fin r
  change even22A317
    (-(33 * (46 * (32000000 + ((i % 317 : ℕ) : ZMod 317)) + 17))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (32000000 + (r.val : ZMod 331)) + 17))) = true →
      (4374501449566023810794718921234288166321856158022357553051836828619864555075133830419138258428227578).testBit r.val = true := by decide

theorem even22_b17_s2_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (32000000 + (i : ZMod 331)) + 17))) = true) :
    (4374501449566023810794718921234288166321856158022357553051836828619864555075133830419138258428227578).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_331_fin r
  change even22A331
    (-(33 * (46 * (32000000 + ((i % 331 : ℕ) : ZMod 331)) + 17))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (32000000 + (r.val : ZMod 337)) + 17))) = true →
      (173882108363309740199186069627372499809158437402481977683624463175261352148611386489452048005910755047).testBit r.val = true := by decide

theorem even22_b17_s2_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (32000000 + (i : ZMod 337)) + 17))) = true) :
    (173882108363309740199186069627372499809158437402481977683624463175261352148611386489452048005910755047).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_337_fin r
  change even22A337
    (-(33 * (46 * (32000000 + ((i % 337 : ℕ) : ZMod 337)) + 17))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (32000000 + (r.val : ZMod 347)) + 17))) = true →
      (282207837514403314615886482906980133048842550367492950732301517977294748300993044882090989168401171054591).testBit r.val = true := by decide

theorem even22_b17_s2_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (32000000 + (i : ZMod 347)) + 17))) = true) :
    (282207837514403314615886482906980133048842550367492950732301517977294748300993044882090989168401171054591).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_347_fin r
  change even22A347
    (-(33 * (46 * (32000000 + ((i % 347 : ℕ) : ZMod 347)) + 17))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (32000000 + (r.val : ZMod 349)) + 17))) = true →
      (1057159518259906575333411104526172199156623458152302672415571284339736599779431458727487854494162691751934).testBit r.val = true := by decide

theorem even22_b17_s2_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (32000000 + (i : ZMod 349)) + 17))) = true) :
    (1057159518259906575333411104526172199156623458152302672415571284339736599779431458727487854494162691751934).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_349_fin r
  change even22A349
    (-(33 * (46 * (32000000 + ((i % 349 : ℕ) : ZMod 349)) + 17))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB17S2Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260738553512049029764507597111165865969269178425648845815083455986377538350456340196816321983) (.leaf 311 4106631704956598627552114124703660736104130033656461855861155743299806371079449435565921923071)) (.node (.leaf 313 16589580894491056543086036920719841251219180742735293186312280741539805039656025808265884467199) (.leaf 317 183561380925074263576960708835989630582873997469675778879266139811409446803816751666543909607167))) (.node (.node (.leaf 331 4374501449566023810794718921234288166321856158022357553051836828619864555075133830419138258428227578) (.leaf 337 173882108363309740199186069627372499809158437402481977683624463175261352148611386489452048005910755047)) (.node (.leaf 347 282207837514403314615886482906980133048842550367492950732301517977294748300993044882090989168401171054591) (.leaf 349 1057159518259906575333411104526172199156623458152302672415571284339736599779431458727487854494162691751934))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S2Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S2Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
