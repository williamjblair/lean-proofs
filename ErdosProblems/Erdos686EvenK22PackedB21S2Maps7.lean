import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s2_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (32000000 + (r.val : ZMod 449)) + 21))) = true →
      (1090241449737745466682780645969034400447208382213962723698890173420989067695496413809205711701834088204935037260793296043380986641117173).testBit r.val = true := by decide

theorem even22_b21_s2_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (32000000 + (i : ZMod 449)) + 21))) = true) :
    (1090241449737745466682780645969034400447208382213962723698890173420989067695496413809205711701834088204935037260793296043380986641117173).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_449_fin r
  change even22A449
    (-(33 * (46 * (32000000 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (32000000 + (r.val : ZMod 457)) + 21))) = true →
      (372135748411732547961515015028084702665244423602332042592515978484166794800926893534801298282479713644112464202805506040831032419382459391).testBit r.val = true := by decide

theorem even22_b21_s2_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (32000000 + (i : ZMod 457)) + 21))) = true) :
    (372135748411732547961515015028084702665244423602332042592515978484166794800926893534801298282479713644112464202805506040831032419382459391).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_457_fin r
  change even22A457
    (-(33 * (46 * (32000000 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (32000000 + (r.val : ZMod 461)) + 21))) = true →
      (5906961527815113028868838553814407602185108125135624899339931636268052331163560010497964133951203373887972875200888968747776755522068283135).testBit r.val = true := by decide

theorem even22_b21_s2_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (32000000 + (i : ZMod 461)) + 21))) = true) :
    (5906961527815113028868838553814407602185108125135624899339931636268052331163560010497964133951203373887972875200888968747776755522068283135).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_461_fin r
  change even22A461
    (-(33 * (46 * (32000000 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (32000000 + (r.val : ZMod 463)) + 21))) = true →
      (22978097542749381085969603808497178902986290064091616070803512930729932614113093211644126045195461627169942534694672834263657986441539874703).testBit r.val = true := by decide

theorem even22_b21_s2_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (32000000 + (i : ZMod 463)) + 21))) = true) :
    (22978097542749381085969603808497178902986290064091616070803512930729932614113093211644126045195461627169942534694672834263657986441539874703).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_463_fin r
  change even22A463
    (-(33 * (46 * (32000000 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (32000000 + (r.val : ZMod 467)) + 21))) = true →
      (184579055763426726845996134850773310981572259325489349638818712401264146492200202274364865105959016878622233689748161405727023000606604001275).testBit r.val = true := by decide

theorem even22_b21_s2_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (32000000 + (i : ZMod 467)) + 21))) = true) :
    (184579055763426726845996134850773310981572259325489349638818712401264146492200202274364865105959016878622233689748161405727023000606604001275).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_467_fin r
  change even22A467
    (-(33 * (46 * (32000000 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (32000000 + (r.val : ZMod 479)) + 21))) = true →
      (1546964727576429829550785633793152286007502666700172432748478805137896101486814208436254540901873968556512126280982700395754776347822324069558141).testBit r.val = true := by decide

theorem even22_b21_s2_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (32000000 + (i : ZMod 479)) + 21))) = true) :
    (1546964727576429829550785633793152286007502666700172432748478805137896101486814208436254540901873968556512126280982700395754776347822324069558141).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_479_fin r
  change even22A479
    (-(33 * (46 * (32000000 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (32000000 + (r.val : ZMod 487)) + 21))) = true →
      (399528913857404430733588822813968152759659375321140224010465654948281741505012072959913048402477453277260635210751786184010364294361872330565484543).testBit r.val = true := by decide

theorem even22_b21_s2_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (32000000 + (i : ZMod 487)) + 21))) = true) :
    (399528913857404430733588822813968152759659375321140224010465654948281741505012072959913048402477453277260635210751786184010364294361872330565484543).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_487_fin r
  change even22A487
    (-(33 * (46 * (32000000 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (32000000 + (r.val : ZMod 491)) + 21))) = true →
      (6391780059614007071009723545431190687166244441715800059784380047727535675852966075703518714542412123156139619348183338437941672652050156178770951165).testBit r.val = true := by decide

theorem even22_b21_s2_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (32000000 + (i : ZMod 491)) + 21))) = true) :
    (6391780059614007071009723545431190687166244441715800059784380047727535675852966075703518714542412123156139619348183338437941672652050156178770951165).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_491_fin r
  change even22A491
    (-(33 * (46 * (32000000 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S2Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1090241449737745466682780645969034400447208382213962723698890173420989067695496413809205711701834088204935037260793296043380986641117173) (.leaf 457 372135748411732547961515015028084702665244423602332042592515978484166794800926893534801298282479713644112464202805506040831032419382459391)) (.node (.leaf 461 5906961527815113028868838553814407602185108125135624899339931636268052331163560010497964133951203373887972875200888968747776755522068283135) (.leaf 463 22978097542749381085969603808497178902986290064091616070803512930729932614113093211644126045195461627169942534694672834263657986441539874703))) (.node (.node (.leaf 467 184579055763426726845996134850773310981572259325489349638818712401264146492200202274364865105959016878622233689748161405727023000606604001275) (.leaf 479 1546964727576429829550785633793152286007502666700172432748478805137896101486814208436254540901873968556512126280982700395754776347822324069558141)) (.node (.leaf 487 399528913857404430733588822813968152759659375321140224010465654948281741505012072959913048402477453277260635210751786184010364294361872330565484543) (.leaf 491 6391780059614007071009723545431190687166244441715800059784380047727535675852966075703518714542412123156139619348183338437941672652050156178770951165))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S2Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S2Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
