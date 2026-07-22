import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (48000000 + (r.val : ZMod 449)) + 21))) = true →
      (1429188515023498827219437772655788063639474195874804865079964135510208690063280907942861106444262930131191291557722426532484336530217471).testBit r.val = true := by decide

theorem even22_b21_s3_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (48000000 + (i : ZMod 449)) + 21))) = true) :
    (1429188515023498827219437772655788063639474195874804865079964135510208690063280907942861106444262930131191291557722426532484336530217471).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_449_fin r
  change even22A449
    (-(33 * (46 * (48000000 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (48000000 + (r.val : ZMod 457)) + 21))) = true →
      (372130069258581613687279693702208016810842844581749437669825881368615858330814607965025869033637611633071647154935524728303397657838090239).testBit r.val = true := by decide

theorem even22_b21_s3_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (48000000 + (i : ZMod 457)) + 21))) = true) :
    (372130069258581613687279693702208016810842844581749437669825881368615858330814607965025869033637611633071647154935524728303397657838090239).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_457_fin r
  change even22A457
    (-(33 * (46 * (48000000 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (48000000 + (r.val : ZMod 461)) + 21))) = true →
      (4465599169110270446628994592202567404792042933711345451898792114449548036396022591287941333790455450006728498499065563862033403554737946603).testBit r.val = true := by decide

theorem even22_b21_s3_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (48000000 + (i : ZMod 461)) + 21))) = true) :
    (4465599169110270446628994592202567404792042933711345451898792114449548036396022591287941333790455450006728498499065563862033403554737946603).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_461_fin r
  change even22A461
    (-(33 * (46 * (48000000 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (48000000 + (r.val : ZMod 463)) + 21))) = true →
      (23069679397988164235007986722919393905356721454007125091489485690918264105013646261361495747760113902568994337163223567548139213240474259197).testBit r.val = true := by decide

theorem even22_b21_s3_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (48000000 + (i : ZMod 463)) + 21))) = true) :
    (23069679397988164235007986722919393905356721454007125091489485690918264105013646261361495747760113902568994337163223567548139213240474259197).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_463_fin r
  change even22A463
    (-(33 * (46 * (48000000 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (48000000 + (r.val : ZMod 467)) + 21))) = true →
      (368975135554793300691120592385486022803148569282162847279260421295688023944313816414743988182166584494446353392790752617677746768934340394973).testBit r.val = true := by decide

theorem even22_b21_s3_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (48000000 + (i : ZMod 467)) + 21))) = true) :
    (368975135554793300691120592385486022803148569282162847279260421295688023944313816414743988182166584494446353392790752617677746768934340394973).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_467_fin r
  change even22A467
    (-(33 * (46 * (48000000 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (48000000 + (r.val : ZMod 479)) + 21))) = true →
      (1045645771779361199824949031098487135510018755959122900094281425954148170850303421879989366391596509173751016986883282688621251390714646175382013).testBit r.val = true := by decide

theorem even22_b21_s3_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (48000000 + (i : ZMod 479)) + 21))) = true) :
    (1045645771779361199824949031098487135510018755959122900094281425954148170850303421879989366391596509173751016986883282688621251390714646175382013).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_479_fin r
  change even22A479
    (-(33 * (46 * (48000000 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (48000000 + (r.val : ZMod 487)) + 21))) = true →
      (349634262732100412736396045979785736244726675123583226661972855709461622199930992155100122797217814900818377657091754879333772595549639763919110079).testBit r.val = true := by decide

theorem even22_b21_s3_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (48000000 + (i : ZMod 487)) + 21))) = true) :
    (349634262732100412736396045979785736244726675123583226661972855709461622199930992155100122797217814900818377657091754879333772595549639763919110079).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_487_fin r
  change even22A487
    (-(33 * (46 * (48000000 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (48000000 + (r.val : ZMod 491)) + 21))) = true →
      (6392950764749696690626839152011222788147160577947171814662270841469075890458543832649302853742386333934116471252299662451468786924937054093188247230).testBit r.val = true := by decide

theorem even22_b21_s3_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (48000000 + (i : ZMod 491)) + 21))) = true) :
    (6392950764749696690626839152011222788147160577947171814662270841469075890458543832649302853742386333934116471252299662451468786924937054093188247230).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_491_fin r
  change even22A491
    (-(33 * (46 * (48000000 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1429188515023498827219437772655788063639474195874804865079964135510208690063280907942861106444262930131191291557722426532484336530217471) (.leaf 457 372130069258581613687279693702208016810842844581749437669825881368615858330814607965025869033637611633071647154935524728303397657838090239)) (.node (.leaf 461 4465599169110270446628994592202567404792042933711345451898792114449548036396022591287941333790455450006728498499065563862033403554737946603) (.leaf 463 23069679397988164235007986722919393905356721454007125091489485690918264105013646261361495747760113902568994337163223567548139213240474259197))) (.node (.node (.leaf 467 368975135554793300691120592385486022803148569282162847279260421295688023944313816414743988182166584494446353392790752617677746768934340394973) (.leaf 479 1045645771779361199824949031098487135510018755959122900094281425954148170850303421879989366391596509173751016986883282688621251390714646175382013)) (.node (.leaf 487 349634262732100412736396045979785736244726675123583226661972855709461622199930992155100122797217814900818377657091754879333772595549639763919110079) (.leaf 491 6392950764749696690626839152011222788147160577947171814662270841469075890458543832649302853742386333934116471252299662451468786924937054093188247230))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
