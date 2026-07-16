import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s4_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (64000000 + (r.val : ZMod 449)) + 29))) = true →
      (1338689223344503495942801510520536011817242891898936270049277090728291999416352466263608393457823593210327313918605125207786872998198239).testBit r.val = true := by decide

theorem even22_b29_s4_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (64000000 + (i : ZMod 449)) + 29))) = true) :
    (1338689223344503495942801510520536011817242891898936270049277090728291999416352466263608393457823593210327313918605125207786872998198239).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_449_fin r
  change even22A449
    (-(33 * (46 * (64000000 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (64000000 + (r.val : ZMod 457)) + 29))) = true →
      (371411748208120584705760890798024228426909408933053578544676848373661942090406060320025985678573876812054134312407136210349977863404387519).testBit r.val = true := by decide

theorem even22_b29_s4_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (64000000 + (i : ZMod 457)) + 29))) = true) :
    (371411748208120584705760890798024228426909408933053578544676848373661942090406060320025985678573876812054134312407136210349977863404387519).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_457_fin r
  change even22A457
    (-(33 * (46 * (64000000 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (64000000 + (r.val : ZMod 461)) + 29))) = true →
      (5941724850301510667405547551167978998003642973753810609578458039201429077320091835481567417698940338853422993019801859346307283553387279839).testBit r.val = true := by decide

theorem even22_b29_s4_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (64000000 + (i : ZMod 461)) + 29))) = true) :
    (5941724850301510667405547551167978998003642973753810609578458039201429077320091835481567417698940338853422993019801859346307283553387279839).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_461_fin r
  change even22A461
    (-(33 * (46 * (64000000 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (64000000 + (r.val : ZMod 463)) + 29))) = true →
      (23817027874790078605923670700763163951019010273536717316926321248611095434083214523099067594349853573977267492168647017315345620270666734845).testBit r.val = true := by decide

theorem even22_b29_s4_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (64000000 + (i : ZMod 463)) + 29))) = true) :
    (23817027874790078605923670700763163951019010273536717316926321248611095434083214523099067594349853573977267492168647017315345620270666734845).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_463_fin r
  change even22A463
    (-(33 * (46 * (64000000 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (64000000 + (r.val : ZMod 467)) + 29))) = true →
      (379583525290503490167064657570656037443079628539476995650341852230116528430984987627477183332468928182090810349505309955462344906925812692731).testBit r.val = true := by decide

theorem even22_b29_s4_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (64000000 + (i : ZMod 467)) + 29))) = true) :
    (379583525290503490167064657570656037443079628539476995650341852230116528430984987627477183332468928182090810349505309955462344906925812692731).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_467_fin r
  change even22A467
    (-(33 * (46 * (64000000 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (64000000 + (r.val : ZMod 479)) + 29))) = true →
      (377997070712124554728112265762752144237061826964162494043532114706800143400046256083694441424820296005770740825331792056093017978256848806849407).testBit r.val = true := by decide

theorem even22_b29_s4_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (64000000 + (i : ZMod 479)) + 29))) = true) :
    (377997070712124554728112265762752144237061826964162494043532114706800143400046256083694441424820296005770740825331792056093017978256848806849407).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_479_fin r
  change even22A479
    (-(33 * (46 * (64000000 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (64000000 + (r.val : ZMod 487)) + 29))) = true →
      (293444220687841573515099257547635686750598676464287695924057101755947311818576673873248086608185013687226169031165949004959229622298994715361542127).testBit r.val = true := by decide

theorem even22_b29_s4_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (64000000 + (i : ZMod 487)) + 29))) = true) :
    (293444220687841573515099257547635686750598676464287695924057101755947311818576673873248086608185013687226169031165949004959229622298994715361542127).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_487_fin r
  change even22A487
    (-(33 * (46 * (64000000 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (64000000 + (r.val : ZMod 491)) + 29))) = true →
      (5886032501471506230811989521633179965170743733810940767641705367280006072362906345718208604046549478150250527175865201912326263497143820658684590591).testBit r.val = true := by decide

theorem even22_b29_s4_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (64000000 + (i : ZMod 491)) + 29))) = true) :
    (5886032501471506230811989521633179965170743733810940767641705367280006072362906345718208604046549478150250527175865201912326263497143820658684590591).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_491_fin r
  change even22A491
    (-(33 * (46 * (64000000 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S4Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1338689223344503495942801510520536011817242891898936270049277090728291999416352466263608393457823593210327313918605125207786872998198239) (.leaf 457 371411748208120584705760890798024228426909408933053578544676848373661942090406060320025985678573876812054134312407136210349977863404387519)) (.node (.leaf 461 5941724850301510667405547551167978998003642973753810609578458039201429077320091835481567417698940338853422993019801859346307283553387279839) (.leaf 463 23817027874790078605923670700763163951019010273536717316926321248611095434083214523099067594349853573977267492168647017315345620270666734845))) (.node (.node (.leaf 467 379583525290503490167064657570656037443079628539476995650341852230116528430984987627477183332468928182090810349505309955462344906925812692731) (.leaf 479 377997070712124554728112265762752144237061826964162494043532114706800143400046256083694441424820296005770740825331792056093017978256848806849407)) (.node (.leaf 487 293444220687841573515099257547635686750598676464287695924057101755947311818576673873248086608185013687226169031165949004959229622298994715361542127) (.leaf 491 5886032501471506230811989521633179965170743733810940767641705367280006072362906345718208604046549478150250527175865201912326263497143820658684590591))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S4Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S4Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
