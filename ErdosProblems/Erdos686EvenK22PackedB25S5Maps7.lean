import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s5_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (80000000 + (r.val : ZMod 449)) + 25))) = true →
      (1453588501130563659271916865826533749020590060880065635558429755668147958636197147871759208986897363463806565092899208603657770605995775).testBit r.val = true := by decide

theorem even22_b25_s5_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (80000000 + (i : ZMod 449)) + 25))) = true) :
    (1453588501130563659271916865826533749020590060880065635558429755668147958636197147871759208986897363463806565092899208603657770605995775).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_449_fin r
  change even22A449
    (-(33 * (46 * (80000000 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (80000000 + (r.val : ZMod 457)) + 25))) = true →
      (370687570553394331345382167991503176640018709112837760719590205683038304094519586331601996989971736817983387875471319086713329198479441886).testBit r.val = true := by decide

theorem even22_b25_s5_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (80000000 + (i : ZMod 457)) + 25))) = true) :
    (370687570553394331345382167991503176640018709112837760719590205683038304094519586331601996989971736817983387875471319086713329198479441886).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_457_fin r
  change even22A457
    (-(33 * (46 * (80000000 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (80000000 + (r.val : ZMod 461)) + 25))) = true →
      (4465424555795679371155236261787157316500286905351560850432613449940709521100188652647633904108809143718287839015014586192392299378091487663).testBit r.val = true := by decide

theorem even22_b25_s5_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (80000000 + (i : ZMod 461)) + 25))) = true) :
    (4465424555795679371155236261787157316500286905351560850432613449940709521100188652647633904108809143718287839015014586192392299378091487663).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_461_fin r
  change even22A461
    (-(33 * (46 * (80000000 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (80000000 + (r.val : ZMod 463)) + 25))) = true →
      (11882308353391439997774163808175286488390252864660068408136299238499929859612826265154173477875766542862373036081457019129830793091819237244).testBit r.val = true := by decide

theorem even22_b25_s5_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (80000000 + (i : ZMod 463)) + 25))) = true) :
    (11882308353391439997774163808175286488390252864660068408136299238499929859612826265154173477875766542862373036081457019129830793091819237244).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_463_fin r
  change even22A463
    (-(33 * (46 * (80000000 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (80000000 + (r.val : ZMod 467)) + 25))) = true →
      (177881188670972230984863806856137790007047924444226613433295395842263480540118411069074394428668270775572826288347428442310845663981885978495).testBit r.val = true := by decide

theorem even22_b25_s5_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (80000000 + (i : ZMod 467)) + 25))) = true) :
    (177881188670972230984863806856137790007047924444226613433295395842263480540118411069074394428668270775572826288347428442310845663981885978495).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_467_fin r
  change even22A467
    (-(33 * (46 * (80000000 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (80000000 + (r.val : ZMod 479)) + 25))) = true →
      (779651171966800210512808767668009798548073103342292854963016314953268521248631792265870384627516011329199143293868325441686743208641683489685367).testBit r.val = true := by decide

theorem even22_b25_s5_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (80000000 + (i : ZMod 479)) + 25))) = true) :
    (779651171966800210512808767668009798548073103342292854963016314953268521248631792265870384627516011329199143293868325441686743208641683489685367).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_479_fin r
  change even22A479
    (-(33 * (46 * (80000000 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (80000000 + (r.val : ZMod 487)) + 25))) = true →
      (324259424041502515890615466638579618212492976666339131572451118363379432800634100807320055167535174971279764287584403260836339325980922175578699647).testBit r.val = true := by decide

theorem even22_b25_s5_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (80000000 + (i : ZMod 487)) + 25))) = true) :
    (324259424041502515890615466638579618212492976666339131572451118363379432800634100807320055167535174971279764287584403260836339325980922175578699647).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_487_fin r
  change even22A487
    (-(33 * (46 * (80000000 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (80000000 + (r.val : ZMod 491)) + 25))) = true →
      (3139552224499133784051357902626481265466619706642553473720196903753863170737358872705492751290598079164162278286884873473292697795462361696358477563).testBit r.val = true := by decide

theorem even22_b25_s5_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (80000000 + (i : ZMod 491)) + 25))) = true) :
    (3139552224499133784051357902626481265466619706642553473720196903753863170737358872705492751290598079164162278286884873473292697795462361696358477563).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_491_fin r
  change even22A491
    (-(33 * (46 * (80000000 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S5Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453588501130563659271916865826533749020590060880065635558429755668147958636197147871759208986897363463806565092899208603657770605995775) (.leaf 457 370687570553394331345382167991503176640018709112837760719590205683038304094519586331601996989971736817983387875471319086713329198479441886)) (.node (.leaf 461 4465424555795679371155236261787157316500286905351560850432613449940709521100188652647633904108809143718287839015014586192392299378091487663) (.leaf 463 11882308353391439997774163808175286488390252864660068408136299238499929859612826265154173477875766542862373036081457019129830793091819237244))) (.node (.node (.leaf 467 177881188670972230984863806856137790007047924444226613433295395842263480540118411069074394428668270775572826288347428442310845663981885978495) (.leaf 479 779651171966800210512808767668009798548073103342292854963016314953268521248631792265870384627516011329199143293868325441686743208641683489685367)) (.node (.leaf 487 324259424041502515890615466638579618212492976666339131572451118363379432800634100807320055167535174971279764287584403260836339325980922175578699647) (.leaf 491 3139552224499133784051357902626481265466619706642553473720196903753863170737358872705492751290598079164162278286884873473292697795462361696358477563))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S5Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S5Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
