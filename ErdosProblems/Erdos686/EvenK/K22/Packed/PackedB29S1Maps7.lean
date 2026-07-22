import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s1_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (16000000 + (r.val : ZMod 449)) + 29))) = true →
      (1449418577846222893800656928848179708359266320944319784922949797127133831520687583353548005631459008016460899856371031497938017135361007).testBit r.val = true := by decide

theorem even22_b29_s1_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (16000000 + (i : ZMod 449)) + 29))) = true) :
    (1449418577846222893800656928848179708359266320944319784922949797127133831520687583353548005631459008016460899856371031497938017135361007).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_449_fin r
  change even22A449
    (-(33 * (46 * (16000000 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (16000000 + (r.val : ZMod 457)) + 29))) = true →
      (371776543507096736450449363542649435357821136632944465899852021444988950955869593428061030459717781187312056661124379053873698131163479031).testBit r.val = true := by decide

theorem even22_b29_s1_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (16000000 + (i : ZMod 457)) + 29))) = true) :
    (371776543507096736450449363542649435357821136632944465899852021444988950955869593428061030459717781187312056661124379053873698131163479031).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_457_fin r
  change even22A457
    (-(33 * (46 * (16000000 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (16000000 + (r.val : ZMod 461)) + 29))) = true →
      (5953172571169535111017774356597754579795813125511748618529631304478611908400936942935613463507044728116806912636957574192055548109056245503).testBit r.val = true := by decide

theorem even22_b29_s1_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (16000000 + (i : ZMod 461)) + 29))) = true) :
    (5953172571169535111017774356597754579795813125511748618529631304478611908400936942935613463507044728116806912636957574192055548109056245503).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_461_fin r
  change even22A461
    (-(33 * (46 * (16000000 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (16000000 + (r.val : ZMod 463)) + 29))) = true →
      (11867728996242995537195541480163679331519073726468294368504581299697280639447062822075522490931825317038534138237203156078517267287056054011).testBit r.val = true := by decide

theorem even22_b29_s1_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (16000000 + (i : ZMod 463)) + 29))) = true) :
    (11867728996242995537195541480163679331519073726468294368504581299697280639447062822075522490931825317038534138237203156078517267287056054011).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_463_fin r
  change even22A463
    (-(33 * (46 * (16000000 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (16000000 + (r.val : ZMod 467)) + 29))) = true →
      (377711912783389580978582428894479954714322161264308639106234021525872856967374151577479074294123279009891015867457288443142852650122673499647).testBit r.val = true := by decide

theorem even22_b29_s1_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (16000000 + (i : ZMod 467)) + 29))) = true) :
    (377711912783389580978582428894479954714322161264308639106234021525872856967374151577479074294123279009891015867457288443142852650122673499647).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_467_fin r
  change even22A467
    (-(33 * (46 * (16000000 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (16000000 + (r.val : ZMod 479)) + 29))) = true →
      (1351846901080719162599922542981261399566738246473141470340744485216115335903244059033144176886793394829675410189732185927730662479159888088907518).testBit r.val = true := by decide

theorem even22_b29_s1_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (16000000 + (i : ZMod 479)) + 29))) = true) :
    (1351846901080719162599922542981261399566738246473141470340744485216115335903244059033144176886793394829675410189732185927730662479159888088907518).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_479_fin r
  change even22A479
    (-(33 * (46 * (16000000 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (16000000 + (r.val : ZMod 487)) + 29))) = true →
      (392510685335185647706424142242940924477252518088795665884674104480577210482882575561000106964395887283425653749295624963398220025802350783228796925).testBit r.val = true := by decide

theorem even22_b29_s1_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (16000000 + (i : ZMod 487)) + 29))) = true) :
    (392510685335185647706424142242940924477252518088795665884674104480577210482882575561000106964395887283425653749295624963398220025802350783228796925).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_487_fin r
  change even22A487
    (-(33 * (46 * (16000000 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (16000000 + (r.val : ZMod 491)) + 29))) = true →
      (3196082990532817010378489914272899471464147688077888954428845773549159701568453538483809694951736540053790565073341849871077757625426961625031630685).testBit r.val = true := by decide

theorem even22_b29_s1_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (16000000 + (i : ZMod 491)) + 29))) = true) :
    (3196082990532817010378489914272899471464147688077888954428845773549159701568453538483809694951736540053790565073341849871077757625426961625031630685).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_491_fin r
  change even22A491
    (-(33 * (46 * (16000000 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S1Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1449418577846222893800656928848179708359266320944319784922949797127133831520687583353548005631459008016460899856371031497938017135361007) (.leaf 457 371776543507096736450449363542649435357821136632944465899852021444988950955869593428061030459717781187312056661124379053873698131163479031)) (.node (.leaf 461 5953172571169535111017774356597754579795813125511748618529631304478611908400936942935613463507044728116806912636957574192055548109056245503) (.leaf 463 11867728996242995537195541480163679331519073726468294368504581299697280639447062822075522490931825317038534138237203156078517267287056054011))) (.node (.node (.leaf 467 377711912783389580978582428894479954714322161264308639106234021525872856967374151577479074294123279009891015867457288443142852650122673499647) (.leaf 479 1351846901080719162599922542981261399566738246473141470340744485216115335903244059033144176886793394829675410189732185927730662479159888088907518)) (.node (.leaf 487 392510685335185647706424142242940924477252518088795665884674104480577210482882575561000106964395887283425653749295624963398220025802350783228796925) (.leaf 491 3196082990532817010378489914272899471464147688077888954428845773549159701568453538483809694951736540053790565073341849871077757625426961625031630685))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S1Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S1Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
