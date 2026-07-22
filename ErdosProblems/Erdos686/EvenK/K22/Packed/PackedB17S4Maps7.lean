import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s4_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (64000000 + (r.val : ZMod 449)) + 17))) = true →
      (1407717654078332528745395627086503813087162660620619809918811003079967851914713265697658322234108442948687151488808706122233616770463743).testBit r.val = true := by decide

theorem even22_b17_s4_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (64000000 + (i : ZMod 449)) + 17))) = true) :
    (1407717654078332528745395627086503813087162660620619809918811003079967851914713265697658322234108442948687151488808706122233616770463743).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_449_fin r
  change even22A449
    (-(33 * (46 * (64000000 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (64000000 + (r.val : ZMod 457)) + 17))) = true →
      (371775157170047023191363725465650960146482256976022246421566298074685427557572718244042023820574308427729740287001236687175814071086741503).testBit r.val = true := by decide

theorem even22_b17_s4_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (64000000 + (i : ZMod 457)) + 17))) = true) :
    (371775157170047023191363725465650960146482256976022246421566298074685427557572718244042023820574308427729740287001236687175814071086741503).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_457_fin r
  change even22A457
    (-(33 * (46 * (64000000 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (64000000 + (r.val : ZMod 461)) + 17))) = true →
      (2221217012023339271859516297422329805870911704395511794470727311713024771778696177213992320422850876642072788733953464678700146537764224995).testBit r.val = true := by decide

theorem even22_b17_s4_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (64000000 + (i : ZMod 461)) + 17))) = true) :
    (2221217012023339271859516297422329805870911704395511794470727311713024771778696177213992320422850876642072788733953464678700146537764224995).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_461_fin r
  change even22A461
    (-(33 * (46 * (64000000 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (64000000 + (r.val : ZMod 463)) + 17))) = true →
      (17489170476160557188933602751638902541791772440448460060388386739670852677946630187115913522937248740959643085504040058982378599401223847935).testBit r.val = true := by decide

theorem even22_b17_s4_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (64000000 + (i : ZMod 463)) + 17))) = true) :
    (17489170476160557188933602751638902541791772440448460060388386739670852677946630187115913522937248740959643085504040058982378599401223847935).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_463_fin r
  change even22A463
    (-(33 * (46 * (64000000 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (64000000 + (r.val : ZMod 467)) + 17))) = true →
      (250054235087491143602589751169797627131538364878444610365094269190670268846892315836439973369192799979504064981456699970567358857228874102774).testBit r.val = true := by decide

theorem even22_b17_s4_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (64000000 + (i : ZMod 467)) + 17))) = true) :
    (250054235087491143602589751169797627131538364878444610365094269190670268846892315836439973369192799979504064981456699970567358857228874102774).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_467_fin r
  change even22A467
    (-(33 * (46 * (64000000 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (64000000 + (r.val : ZMod 479)) + 17))) = true →
      (1557623235660244060825699637212971643442151383044076026006682831078869574616366188460025257682941943770631255086482692469713482169618162949470905).testBit r.val = true := by decide

theorem even22_b17_s4_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (64000000 + (i : ZMod 479)) + 17))) = true) :
    (1557623235660244060825699637212971643442151383044076026006682831078869574616366188460025257682941943770631255086482692469713482169618162949470905).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_479_fin r
  change even22A479
    (-(33 * (46 * (64000000 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (64000000 + (r.val : ZMod 487)) + 17))) = true →
      (374400986220520581279519433750644079176487179884098423398521242071447947104642995911069214611345157440951493488659383228708334635693217426895200220).testBit r.val = true := by decide

theorem even22_b17_s4_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (64000000 + (i : ZMod 487)) + 17))) = true) :
    (374400986220520581279519433750644079176487179884098423398521242071447947104642995911069214611345157440951493488659383228708334635693217426895200220).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_487_fin r
  change even22A487
    (-(33 * (46 * (64000000 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (64000000 + (r.val : ZMod 491)) + 17))) = true →
      (6380753432085309546868207913157851168833829125679835620940646154254925521566092976512663421534571682632917798319402748606170316965105542056062613209).testBit r.val = true := by decide

theorem even22_b17_s4_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (64000000 + (i : ZMod 491)) + 17))) = true) :
    (6380753432085309546868207913157851168833829125679835620940646154254925521566092976512663421534571682632917798319402748606170316965105542056062613209).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_491_fin r
  change even22A491
    (-(33 * (46 * (64000000 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S4Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1407717654078332528745395627086503813087162660620619809918811003079967851914713265697658322234108442948687151488808706122233616770463743) (.leaf 457 371775157170047023191363725465650960146482256976022246421566298074685427557572718244042023820574308427729740287001236687175814071086741503)) (.node (.leaf 461 2221217012023339271859516297422329805870911704395511794470727311713024771778696177213992320422850876642072788733953464678700146537764224995) (.leaf 463 17489170476160557188933602751638902541791772440448460060388386739670852677946630187115913522937248740959643085504040058982378599401223847935))) (.node (.node (.leaf 467 250054235087491143602589751169797627131538364878444610365094269190670268846892315836439973369192799979504064981456699970567358857228874102774) (.leaf 479 1557623235660244060825699637212971643442151383044076026006682831078869574616366188460025257682941943770631255086482692469713482169618162949470905)) (.node (.leaf 487 374400986220520581279519433750644079176487179884098423398521242071447947104642995911069214611345157440951493488659383228708334635693217426895200220) (.leaf 491 6380753432085309546868207913157851168833829125679835620940646154254925521566092976512663421534571682632917798319402748606170316965105542056062613209))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S4Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S4Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
