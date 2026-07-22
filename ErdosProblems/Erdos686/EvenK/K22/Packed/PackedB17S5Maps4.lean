import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s5_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (80000000 + (r.val : ZMod 307)) + 17))) = true →
      (194536850224094430538875487626271967120668846105268725998911837563240865746046036356739629051).testBit r.val = true := by decide

theorem even22_b17_s5_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (80000000 + (i : ZMod 307)) + 17))) = true) :
    (194536850224094430538875487626271967120668846105268725998911837563240865746046036356739629051).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_307_fin r
  change even22A307
    (-(33 * (46 * (80000000 + ((i % 307 : ℕ) : ZMod 307)) + 17))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (80000000 + (r.val : ZMod 311)) + 17))) = true →
      (4171848653788675250650112665229617833501384605394872351297508495373277060191195498505289334717).testBit r.val = true := by decide

theorem even22_b17_s5_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (80000000 + (i : ZMod 311)) + 17))) = true) :
    (4171848653788675250650112665229617833501384605394872351297508495373277060191195498505289334717).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_311_fin r
  change even22A311
    (-(33 * (46 * (80000000 + ((i % 311 : ℕ) : ZMod 311)) + 17))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (80000000 + (r.val : ZMod 313)) + 17))) = true →
      (16687398716673210748782947318211572969217369376878010267367953422782664897292842022004298612735).testBit r.val = true := by decide

theorem even22_b17_s5_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (80000000 + (i : ZMod 313)) + 17))) = true) :
    (16687398716673210748782947318211572969217369376878010267367953422782664897292842022004298612735).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_313_fin r
  change even22A313
    (-(33 * (46 * (80000000 + ((i % 313 : ℕ) : ZMod 313)) + 17))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (80000000 + (r.val : ZMod 317)) + 17))) = true →
      (191511937315086466634721736282139719843121843828587895578398143929889880746458055360510598970363).testBit r.val = true := by decide

theorem even22_b17_s5_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (80000000 + (i : ZMod 317)) + 17))) = true) :
    (191511937315086466634721736282139719843121843828587895578398143929889880746458055360510598970363).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_317_fin r
  change even22A317
    (-(33 * (46 * (80000000 + ((i % 317 : ℕ) : ZMod 317)) + 17))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (80000000 + (r.val : ZMod 331)) + 17))) = true →
      (1639870149913058767305775504912030550368602189128042420416917387852096278210790759349918240572152623).testBit r.val = true := by decide

theorem even22_b17_s5_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (80000000 + (i : ZMod 331)) + 17))) = true) :
    (1639870149913058767305775504912030550368602189128042420416917387852096278210790759349918240572152623).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_331_fin r
  change even22A331
    (-(33 * (46 * (80000000 + ((i % 331 : ℕ) : ZMod 331)) + 17))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (80000000 + (r.val : ZMod 337)) + 17))) = true →
      (262465800398352022280898051097105484852983845187535358820859198220683913871965130456246198955314839294).testBit r.val = true := by decide

theorem even22_b17_s5_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (80000000 + (i : ZMod 337)) + 17))) = true) :
    (262465800398352022280898051097105484852983845187535358820859198220683913871965130456246198955314839294).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_337_fin r
  change even22A337
    (-(33 * (46 * (80000000 + ((i % 337 : ℕ) : ZMod 337)) + 17))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (80000000 + (r.val : ZMod 347)) + 17))) = true →
      (285567454594294220891791149290556024857573426388993162711030942117305792384505885556847926729243120107519).testBit r.val = true := by decide

theorem even22_b17_s5_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (80000000 + (i : ZMod 347)) + 17))) = true) :
    (285567454594294220891791149290556024857573426388993162711030942117305792384505885556847926729243120107519).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_347_fin r
  change even22A347
    (-(33 * (46 * (80000000 + ((i % 347 : ℕ) : ZMod 347)) + 17))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (80000000 + (r.val : ZMod 349)) + 17))) = true →
      (859991980420661543086474112323149791706488607502786993621781382069276070912870863619318314581642932781055).testBit r.val = true := by decide

theorem even22_b17_s5_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (80000000 + (i : ZMod 349)) + 17))) = true) :
    (859991980420661543086474112323149791706488607502786993621781382069276070912870863619318314581642932781055).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_349_fin r
  change even22A349
    (-(33 * (46 * (80000000 + ((i % 349 : ℕ) : ZMod 349)) + 17))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB17S5Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 194536850224094430538875487626271967120668846105268725998911837563240865746046036356739629051) (.leaf 311 4171848653788675250650112665229617833501384605394872351297508495373277060191195498505289334717)) (.node (.leaf 313 16687398716673210748782947318211572969217369376878010267367953422782664897292842022004298612735) (.leaf 317 191511937315086466634721736282139719843121843828587895578398143929889880746458055360510598970363))) (.node (.node (.leaf 331 1639870149913058767305775504912030550368602189128042420416917387852096278210790759349918240572152623) (.leaf 337 262465800398352022280898051097105484852983845187535358820859198220683913871965130456246198955314839294)) (.node (.leaf 347 285567454594294220891791149290556024857573426388993162711030942117305792384505885556847926729243120107519) (.leaf 349 859991980420661543086474112323149791706488607502786993621781382069276070912870863619318314581642932781055))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S5Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S5Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
