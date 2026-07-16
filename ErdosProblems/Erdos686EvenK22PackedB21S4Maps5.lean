import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s4_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (64000000 + (r.val : ZMod 353)) + 21))) = true →
      (12596313354713893554516752795744557455988162849734988267666426462757480716182689262184089527927424779549661).testBit r.val = true := by decide

theorem even22_b21_s4_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (64000000 + (i : ZMod 353)) + 21))) = true) :
    (12596313354713893554516752795744557455988162849734988267666426462757480716182689262184089527927424779549661).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_353_fin r
  change even22A353
    (-(33 * (46 * (64000000 + ((i % 353 : ℕ) : ZMod 353)) + 21))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (64000000 + (r.val : ZMod 359)) + 21))) = true →
      (1169684293607389478964438060743786846664955595017190897331698869908455546171597898922621026167884924294528895).testBit r.val = true := by decide

theorem even22_b21_s4_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (64000000 + (i : ZMod 359)) + 21))) = true) :
    (1169684293607389478964438060743786846664955595017190897331698869908455546171597898922621026167884924294528895).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_359_fin r
  change even22A359
    (-(33 * (46 * (64000000 + ((i % 359 : ℕ) : ZMod 359)) + 21))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (64000000 + (r.val : ZMod 367)) + 21))) = true →
      (291054139387049079277621270910298911193564340698887696062693650253334142794284529549836691201415609296319660014).testBit r.val = true := by decide

theorem even22_b21_s4_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (64000000 + (i : ZMod 367)) + 21))) = true) :
    (291054139387049079277621270910298911193564340698887696062693650253334142794284529549836691201415609296319660014).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_367_fin r
  change even22A367
    (-(33 * (46 * (64000000 + ((i % 367 : ℕ) : ZMod 367)) + 21))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (64000000 + (r.val : ZMod 373)) + 21))) = true →
      (9619552399493286698873073961704102916000196378317007326782686510857122838691219215849563286484985602466159525373).testBit r.val = true := by decide

theorem even22_b21_s4_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (64000000 + (i : ZMod 373)) + 21))) = true) :
    (9619552399493286698873073961704102916000196378317007326782686510857122838691219215849563286484985602466159525373).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_373_fin r
  change even22A373
    (-(33 * (46 * (64000000 + ((i % 373 : ℕ) : ZMod 373)) + 21))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (64000000 + (r.val : ZMod 379)) + 21))) = true →
      (1230692660047486212620536297245643158728837127237457863544573150160048310960577207769726277382684964153019705851775).testBit r.val = true := by decide

theorem even22_b21_s4_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (64000000 + (i : ZMod 379)) + 21))) = true) :
    (1230692660047486212620536297245643158728837127237457863544573150160048310960577207769726277382684964153019705851775).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_379_fin r
  change even22A379
    (-(33 * (46 * (64000000 + ((i % 379 : ℕ) : ZMod 379)) + 21))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (64000000 + (r.val : ZMod 383)) + 21))) = true →
      (18469685560386229872652599084503174698449812282318767392857879369276330737402859269988348433097379373984673028308697).testBit r.val = true := by decide

theorem even22_b21_s4_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (64000000 + (i : ZMod 383)) + 21))) = true) :
    (18469685560386229872652599084503174698449812282318767392857879369276330737402859269988348433097379373984673028308697).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_383_fin r
  change even22A383
    (-(33 * (46 * (64000000 + ((i % 383 : ℕ) : ZMod 383)) + 21))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (64000000 + (r.val : ZMod 389)) + 21))) = true →
      (1260864047975602281408864650683995592360790757564304541974082213792069414040416620991972757453454422690430047381093375).testBit r.val = true := by decide

theorem even22_b21_s4_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (64000000 + (i : ZMod 389)) + 21))) = true) :
    (1260864047975602281408864650683995592360790757564304541974082213792069414040416620991972757453454422690430047381093375).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_389_fin r
  change even22A389
    (-(33 * (46 * (64000000 + ((i % 389 : ℕ) : ZMod 389)) + 21))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (64000000 + (r.val : ZMod 397)) + 21))) = true →
      (322770768602966509633446312733494532537544389163212750090729059726871319687115368617627316212828550625719292870122274791).testBit r.val = true := by decide

theorem even22_b21_s4_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (64000000 + (i : ZMod 397)) + 21))) = true) :
    (322770768602966509633446312733494532537544389163212750090729059726871319687115368617627316212828550625719292870122274791).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_397_fin r
  change even22A397
    (-(33 * (46 * (64000000 + ((i % 397 : ℕ) : ZMod 397)) + 21))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB21S4Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 12596313354713893554516752795744557455988162849734988267666426462757480716182689262184089527927424779549661) (.leaf 359 1169684293607389478964438060743786846664955595017190897331698869908455546171597898922621026167884924294528895)) (.node (.leaf 367 291054139387049079277621270910298911193564340698887696062693650253334142794284529549836691201415609296319660014) (.leaf 373 9619552399493286698873073961704102916000196378317007326782686510857122838691219215849563286484985602466159525373))) (.node (.node (.leaf 379 1230692660047486212620536297245643158728837127237457863544573150160048310960577207769726277382684964153019705851775) (.leaf 383 18469685560386229872652599084503174698449812282318767392857879369276330737402859269988348433097379373984673028308697)) (.node (.leaf 389 1260864047975602281408864650683995592360790757564304541974082213792069414040416620991972757453454422690430047381093375) (.leaf 397 322770768602966509633446312733494532537544389163212750090729059726871319687115368617627316212828550625719292870122274791))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S4Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S4Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
