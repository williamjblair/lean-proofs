import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (0 + (r.val : ZMod 307)) + 17))) = true →
      (257430405709908803768078858770733018656487364680845679994356483500455380464986601520767827829).testBit r.val = true := by decide

theorem even22_b17_s0_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (0 + (i : ZMod 307)) + 17))) = true) :
    (257430405709908803768078858770733018656487364680845679994356483500455380464986601520767827829).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_307_fin r
  change even22A307
    (-(33 * (46 * (0 + ((i % 307 : ℕ) : ZMod 307)) + 17))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (0 + (r.val : ZMod 311)) + 17))) = true →
      (4171594055385716688594100993152048302324621880734429147684321769504691328447718331845324046207).testBit r.val = true := by decide

theorem even22_b17_s0_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (0 + (i : ZMod 311)) + 17))) = true) :
    (4171594055385716688594100993152048302324621880734429147684321769504691328447718331845324046207).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_311_fin r
  change even22A311
    (-(33 * (46 * (0 + ((i % 311 : ℕ) : ZMod 311)) + 17))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (0 + (r.val : ZMod 313)) + 17))) = true →
      (16687207497287001994954882085376493984941702023036688446995883577565310199127538931305136783359).testBit r.val = true := by decide

theorem even22_b17_s0_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (0 + (i : ZMod 313)) + 17))) = true) :
    (16687207497287001994954882085376493984941702023036688446995883577565310199127538931305136783359).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_313_fin r
  change even22A313
    (-(33 * (46 * (0 + ((i % 313 : ℕ) : ZMod 313)) + 17))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (0 + (r.val : ZMod 317)) + 17))) = true →
      (258589222352937675122232360769538979700601365083620327137122955548924084777961413737814710811519).testBit r.val = true := by decide

theorem even22_b17_s0_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (0 + (i : ZMod 317)) + 17))) = true) :
    (258589222352937675122232360769538979700601365083620327137122955548924084777961413737814710811519).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_317_fin r
  change even22A317
    (-(33 * (46 * (0 + ((i % 317 : ℕ) : ZMod 317)) + 17))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (0 + (r.val : ZMod 331)) + 17))) = true →
      (3819067558991749012254989944457295850047886800710387819257613583437588254707144748954828004046929599).testBit r.val = true := by decide

theorem even22_b17_s0_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (0 + (i : ZMod 331)) + 17))) = true) :
    (3819067558991749012254989944457295850047886800710387819257613583437588254707144748954828004046929599).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_331_fin r
  change even22A331
    (-(33 * (46 * (0 + ((i % 331 : ℕ) : ZMod 331)) + 17))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (0 + (r.val : ZMod 337)) + 17))) = true →
      (279416864138870661273570189570624197268171395454530964785985554687765490324311328802254147352396298227).testBit r.val = true := by decide

theorem even22_b17_s0_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (0 + (i : ZMod 337)) + 17))) = true) :
    (279416864138870661273570189570624197268171395454530964785985554687765490324311328802254147352396298227).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_337_fin r
  change even22A337
    (-(33 * (46 * (0 + ((i % 337 : ℕ) : ZMod 337)) + 17))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (0 + (r.val : ZMod 347)) + 17))) = true →
      (286687326998756901914393322998348580305518491284705135334768685673057843644534618813606721209636042571773).testBit r.val = true := by decide

theorem even22_b17_s0_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (0 + (i : ZMod 347)) + 17))) = true) :
    (286687326998756901914393322998348580305518491284705135334768685673057843644534618813606721209636042571773).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_347_fin r
  change even22A347
    (-(33 * (46 * (0 + ((i % 347 : ℕ) : ZMod 347)) + 17))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (0 + (r.val : ZMod 349)) + 17))) = true →
      (215015495080109260107186004073394889329738073789004165257460026475494630597759581187555600023651396615870).testBit r.val = true := by decide

theorem even22_b17_s0_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (0 + (i : ZMod 349)) + 17))) = true) :
    (215015495080109260107186004073394889329738073789004165257460026475494630597759581187555600023651396615870).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_349_fin r
  change even22A349
    (-(33 * (46 * (0 + ((i % 349 : ℕ) : ZMod 349)) + 17))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 257430405709908803768078858770733018656487364680845679994356483500455380464986601520767827829) (.leaf 311 4171594055385716688594100993152048302324621880734429147684321769504691328447718331845324046207)) (.node (.leaf 313 16687207497287001994954882085376493984941702023036688446995883577565310199127538931305136783359) (.leaf 317 258589222352937675122232360769538979700601365083620327137122955548924084777961413737814710811519))) (.node (.node (.leaf 331 3819067558991749012254989944457295850047886800710387819257613583437588254707144748954828004046929599) (.leaf 337 279416864138870661273570189570624197268171395454530964785985554687765490324311328802254147352396298227)) (.node (.leaf 347 286687326998756901914393322998348580305518491284705135334768685673057843644534618813606721209636042571773) (.leaf 349 215015495080109260107186004073394889329738073789004165257460026475494630597759581187555600023651396615870))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
