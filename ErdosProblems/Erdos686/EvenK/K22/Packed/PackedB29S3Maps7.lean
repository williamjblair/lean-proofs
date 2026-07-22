import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s3_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (48000000 + (r.val : ZMod 449)) + 29))) = true →
      (1430960965787281541472652062322377013803842987531158663312739671285304674557259037821813787403697941935430027519273767776627115591170943).testBit r.val = true := by decide

theorem even22_b29_s3_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (48000000 + (i : ZMod 449)) + 29))) = true) :
    (1430960965787281541472652062322377013803842987531158663312739671285304674557259037821813787403697941935430027519273767776627115591170943).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_449_fin r
  change even22A449
    (-(33 * (46 * (48000000 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (48000000 + (r.val : ZMod 457)) + 29))) = true →
      (348880280795269269493879015954223397239083922477500203978549652730028589889590465876832194170355797027540381073227663857780634647353335807).testBit r.val = true := by decide

theorem even22_b29_s3_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (48000000 + (i : ZMod 457)) + 29))) = true) :
    (348880280795269269493879015954223397239083922477500203978549652730028589889590465876832194170355797027540381073227663857780634647353335807).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_457_fin r
  change even22A457
    (-(33 * (46 * (48000000 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (48000000 + (r.val : ZMod 461)) + 29))) = true →
      (5853959052203400125323694976708996756140056646795783837439317769648270312591252069831616127412989594365939323898689266144477182581721235454).testBit r.val = true := by decide

theorem even22_b29_s3_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (48000000 + (i : ZMod 461)) + 29))) = true) :
    (5853959052203400125323694976708996756140056646795783837439317769648270312591252069831616127412989594365939323898689266144477182581721235454).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_461_fin r
  change even22A461
    (-(33 * (46 * (48000000 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (48000000 + (r.val : ZMod 463)) + 29))) = true →
      (17798803234768890078929733988930118859300155290610988954235740285358653689024387425420834369965027105753860239938680100785119648414158389231).testBit r.val = true := by decide

theorem even22_b29_s3_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (48000000 + (i : ZMod 463)) + 29))) = true) :
    (17798803234768890078929733988930118859300155290610988954235740285358653689024387425420834369965027105753860239938680100785119648414158389231).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_463_fin r
  change even22A463
    (-(33 * (46 * (48000000 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (48000000 + (r.val : ZMod 467)) + 29))) = true →
      (343649257947715584765064027924046993335501133470316761676907387078961132820351623470456391553973436032142204372847793352859417616619815559125).testBit r.val = true := by decide

theorem even22_b29_s3_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (48000000 + (i : ZMod 467)) + 29))) = true) :
    (343649257947715584765064027924046993335501133470316761676907387078961132820351623470456391553973436032142204372847793352859417616619815559125).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_467_fin r
  change even22A467
    (-(33 * (46 * (48000000 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (48000000 + (r.val : ZMod 479)) + 29))) = true →
      (1535340661899599207226460120055853449095782746229942877755131203399002998557567861376742506778893918619206317241471295064288558157120758135782839).testBit r.val = true := by decide

theorem even22_b29_s3_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (48000000 + (i : ZMod 479)) + 29))) = true) :
    (1535340661899599207226460120055853449095782746229942877755131203399002998557567861376742506778893918619206317241471295064288558157120758135782839).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_479_fin r
  change even22A479
    (-(33 * (46 * (48000000 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (48000000 + (r.val : ZMod 487)) + 29))) = true →
      (293442744029911054500129226127968157440260186648163118221592092377953425700136194410636059132895833221216376483883069489956091772626341572208492535).testBit r.val = true := by decide

theorem even22_b29_s3_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (48000000 + (i : ZMod 487)) + 29))) = true) :
    (293442744029911054500129226127968157440260186648163118221592092377953425700136194410636059132895833221216376483883069489956091772626341572208492535).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_487_fin r
  change even22A487
    (-(33 * (46 * (48000000 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (48000000 + (r.val : ZMod 491)) + 29))) = true →
      (4769983001607103984435424291146501381392142900260558821868614991502421949303810975233134687906313737293590787886362020059846345176079935643397348263).testBit r.val = true := by decide

theorem even22_b29_s3_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (48000000 + (i : ZMod 491)) + 29))) = true) :
    (4769983001607103984435424291146501381392142900260558821868614991502421949303810975233134687906313737293590787886362020059846345176079935643397348263).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_491_fin r
  change even22A491
    (-(33 * (46 * (48000000 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S3Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1430960965787281541472652062322377013803842987531158663312739671285304674557259037821813787403697941935430027519273767776627115591170943) (.leaf 457 348880280795269269493879015954223397239083922477500203978549652730028589889590465876832194170355797027540381073227663857780634647353335807)) (.node (.leaf 461 5853959052203400125323694976708996756140056646795783837439317769648270312591252069831616127412989594365939323898689266144477182581721235454) (.leaf 463 17798803234768890078929733988930118859300155290610988954235740285358653689024387425420834369965027105753860239938680100785119648414158389231))) (.node (.node (.leaf 467 343649257947715584765064027924046993335501133470316761676907387078961132820351623470456391553973436032142204372847793352859417616619815559125) (.leaf 479 1535340661899599207226460120055853449095782746229942877755131203399002998557567861376742506778893918619206317241471295064288558157120758135782839)) (.node (.leaf 487 293442744029911054500129226127968157440260186648163118221592092377953425700136194410636059132895833221216376483883069489956091772626341572208492535) (.leaf 491 4769983001607103984435424291146501381392142900260558821868614991502421949303810975233134687906313737293590787886362020059846345176079935643397348263))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S3Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S3Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
