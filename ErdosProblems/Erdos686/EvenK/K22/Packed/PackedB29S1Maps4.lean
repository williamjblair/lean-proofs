import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s1_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (16000000 + (r.val : ZMod 307)) + 29))) = true →
      (227129504561953090691419778353719239711762566914389780325553213887497578965284837105920376831).testBit r.val = true := by decide

theorem even22_b29_s1_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (16000000 + (i : ZMod 307)) + 29))) = true) :
    (227129504561953090691419778353719239711762566914389780325553213887497578965284837105920376831).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_307_fin r
  change even22A307
    (-(33 * (46 * (16000000 + ((i % 307 : ℕ) : ZMod 307)) + 29))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (16000000 + (r.val : ZMod 311)) + 29))) = true →
      (4155489721720739658426799357696987204932289986568900825087813520332220808639250598572924599807).testBit r.val = true := by decide

theorem even22_b29_s1_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (16000000 + (i : ZMod 311)) + 29))) = true) :
    (4155489721720739658426799357696987204932289986568900825087813520332220808639250598572924599807).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_311_fin r
  change even22A311
    (-(33 * (46 * (16000000 + ((i % 311 : ℕ) : ZMod 311)) + 29))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (16000000 + (r.val : ZMod 313)) + 29))) = true →
      (16654806111420422951196622930119717830821088643933692617576681857994521588539473937750495848439).testBit r.val = true := by decide

theorem even22_b29_s1_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (16000000 + (i : ZMod 313)) + 29))) = true) :
    (16654806111420422951196622930119717830821088643933692617576681857994521588539473937750495848439).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_313_fin r
  change even22A313
    (-(33 * (46 * (16000000 + ((i % 313 : ℕ) : ZMod 313)) + 29))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (16000000 + (r.val : ZMod 317)) + 29))) = true →
      (266998249156213991282161967642956223526000936860632563493311579703834978962794587138844488101887).testBit r.val = true := by decide

theorem even22_b29_s1_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (16000000 + (i : ZMod 317)) + 29))) = true) :
    (266998249156213991282161967642956223526000936860632563493311579703834978962794587138844488101887).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_317_fin r
  change even22A317
    (-(33 * (46 * (16000000 + ((i % 317 : ℕ) : ZMod 317)) + 29))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (16000000 + (r.val : ZMod 331)) + 29))) = true →
      (4374501449486436331538900436368634684035174640478572283202807327506956986229202928871525125623644159).testBit r.val = true := by decide

theorem even22_b29_s1_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (16000000 + (i : ZMod 331)) + 29))) = true) :
    (4374501449486436331538900436368634684035174640478572283202807327506956986229202928871525125623644159).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_331_fin r
  change even22A331
    (-(33 * (46 * (16000000 + ((i % 331 : ℕ) : ZMod 331)) + 29))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (16000000 + (r.val : ZMod 337)) + 29))) = true →
      (200393897708974801092832604668118404886256115994048615706483537210939236931556282254943853140800167935).testBit r.val = true := by decide

theorem even22_b29_s1_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (16000000 + (i : ZMod 337)) + 29))) = true) :
    (200393897708974801092832604668118404886256115994048615706483537210939236931556282254943853140800167935).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_337_fin r
  change even22A337
    (-(33 * (46 * (16000000 + ((i % 337 : ℕ) : ZMod 337)) + 29))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (16000000 + (r.val : ZMod 347)) + 29))) = true →
      (286669828992952463054678018675531579368229078953513772850246882776157726804585311995993790239183200057343).testBit r.val = true := by decide

theorem even22_b29_s1_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (16000000 + (i : ZMod 347)) + 29))) = true) :
    (286669828992952463054678018675531579368229078953513772850246882776157726804585311995993790239183200057343).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_347_fin r
  change even22A347
    (-(33 * (46 * (16000000 + ((i % 347 : ℕ) : ZMod 347)) + 29))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (16000000 + (r.val : ZMod 349)) + 29))) = true →
      (1003405505589227866809282889103318455787719927368022565749067307298329585186422204717653751471281417485823).testBit r.val = true := by decide

theorem even22_b29_s1_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (16000000 + (i : ZMod 349)) + 29))) = true) :
    (1003405505589227866809282889103318455787719927368022565749067307298329585186422204717653751471281417485823).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_349_fin r
  change even22A349
    (-(33 * (46 * (16000000 + ((i % 349 : ℕ) : ZMod 349)) + 29))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB29S1Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 227129504561953090691419778353719239711762566914389780325553213887497578965284837105920376831) (.leaf 311 4155489721720739658426799357696987204932289986568900825087813520332220808639250598572924599807)) (.node (.leaf 313 16654806111420422951196622930119717830821088643933692617576681857994521588539473937750495848439) (.leaf 317 266998249156213991282161967642956223526000936860632563493311579703834978962794587138844488101887))) (.node (.node (.leaf 331 4374501449486436331538900436368634684035174640478572283202807327506956986229202928871525125623644159) (.leaf 337 200393897708974801092832604668118404886256115994048615706483537210939236931556282254943853140800167935)) (.node (.leaf 347 286669828992952463054678018675531579368229078953513772850246882776157726804585311995993790239183200057343) (.leaf 349 1003405505589227866809282889103318455787719927368022565749067307298329585186422204717653751471281417485823))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S1Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S1Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
