import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s4_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (64000000 + (r.val : ZMod 307)) + 21))) = true →
      (260609311635868436417034000913435885107922035333495158175579829176296529583263820916203715711).testBit r.val = true := by decide

theorem even22_b21_s4_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (64000000 + (i : ZMod 307)) + 21))) = true) :
    (260609311635868436417034000913435885107922035333495158175579829176296529583263820916203715711).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_307_fin r
  change even22A307
    (-(33 * (46 * (64000000 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (64000000 + (r.val : ZMod 311)) + 21))) = true →
      (2085916851512014098640006376098964588704543152270953024450766032441133949811283232434950208511).testBit r.val = true := by decide

theorem even22_b21_s4_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (64000000 + (i : ZMod 311)) + 21))) = true) :
    (2085916851512014098640006376098964588704543152270953024450766032441133949811283232434950208511).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_311_fin r
  change even22A311
    (-(33 * (46 * (64000000 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (64000000 + (r.val : ZMod 313)) + 21))) = true →
      (15122313539875254408709984539773071589502455670094444502827553447970506519577598476438281912319).testBit r.val = true := by decide

theorem even22_b21_s4_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (64000000 + (i : ZMod 313)) + 21))) = true) :
    (15122313539875254408709984539773071589502455670094444502827553447970506519577598476438281912319).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_313_fin r
  change even22A313
    (-(33 * (46 * (64000000 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (64000000 + (r.val : ZMod 317)) + 21))) = true →
      (265881699841543953331738878476200039372424424198249252409748850527622194777397996205600885178238).testBit r.val = true := by decide

theorem even22_b21_s4_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (64000000 + (i : ZMod 317)) + 21))) = true) :
    (265881699841543953331738878476200039372424424198249252409748850527622194777397996205600885178238).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_317_fin r
  change even22A317
    (-(33 * (46 * (64000000 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (64000000 + (r.val : ZMod 331)) + 21))) = true →
      (3800771342251014944272578657372178105823923443101957119622735229841274984074353809565529327039133163).testBit r.val = true := by decide

theorem even22_b21_s4_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (64000000 + (i : ZMod 331)) + 21))) = true) :
    (3800771342251014944272578657372178105823923443101957119622735229841274984074353809565529327039133163).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_331_fin r
  change even22A331
    (-(33 * (46 * (64000000 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (64000000 + (r.val : ZMod 337)) + 21))) = true →
      (279421013078387051772312798312816235766842767812578060081629186077223005470788489892492775469437394367).testBit r.val = true := by decide

theorem even22_b21_s4_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (64000000 + (i : ZMod 337)) + 21))) = true) :
    (279421013078387051772312798312816235766842767812578060081629186077223005470788489892492775469437394367).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_337_fin r
  change even22A337
    (-(33 * (46 * (64000000 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (64000000 + (r.val : ZMod 347)) + 21))) = true →
      (286687326998754864877434034083936293011466358923375130202338766422750327778008636618461123280506374324219).testBit r.val = true := by decide

theorem even22_b21_s4_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (64000000 + (i : ZMod 347)) + 21))) = true) :
    (286687326998754864877434034083936293011466358923375130202338766422750327778008636618461123280506374324219).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_347_fin r
  change even22A347
    (-(33 * (46 * (64000000 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (64000000 + (r.val : ZMod 349)) + 21))) = true →
      (1141919858394527299023076815655825053438751472978609396043317788619058366652410164389140016013594237828863).testBit r.val = true := by decide

theorem even22_b21_s4_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (64000000 + (i : ZMod 349)) + 21))) = true) :
    (1141919858394527299023076815655825053438751472978609396043317788619058366652410164389140016013594237828863).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_349_fin r
  change even22A349
    (-(33 * (46 * (64000000 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S4Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260609311635868436417034000913435885107922035333495158175579829176296529583263820916203715711) (.leaf 311 2085916851512014098640006376098964588704543152270953024450766032441133949811283232434950208511)) (.node (.leaf 313 15122313539875254408709984539773071589502455670094444502827553447970506519577598476438281912319) (.leaf 317 265881699841543953331738878476200039372424424198249252409748850527622194777397996205600885178238))) (.node (.node (.leaf 331 3800771342251014944272578657372178105823923443101957119622735229841274984074353809565529327039133163) (.leaf 337 279421013078387051772312798312816235766842767812578060081629186077223005470788489892492775469437394367)) (.node (.leaf 347 286687326998754864877434034083936293011466358923375130202338766422750327778008636618461123280506374324219) (.leaf 349 1141919858394527299023076815655825053438751472978609396043317788619058366652410164389140016013594237828863))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S4Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S4Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
