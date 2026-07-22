import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s5_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (80000000 + (r.val : ZMod 449)) + 29))) = true →
      (1453574854397159281405606482237533488213390968334597453158191461000512875477847690554446519645173798679309709069334183088815245214318585).testBit r.val = true := by decide

theorem even22_b29_s5_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (80000000 + (i : ZMod 449)) + 29))) = true) :
    (1453574854397159281405606482237533488213390968334597453158191461000512875477847690554446519645173798679309709069334183088815245214318585).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_449_fin r
  change even22A449
    (-(33 * (46 * (80000000 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (80000000 + (r.val : ZMod 457)) + 29))) = true →
      (279106025418860054796041674008269497129122186053771946109952275952662141678518864200507001194526508902244504992268198771006731129152338943).testBit r.val = true := by decide

theorem even22_b29_s5_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (80000000 + (i : ZMod 457)) + 29))) = true) :
    (279106025418860054796041674008269497129122186053771946109952275952662141678518864200507001194526508902244504992268198771006731129152338943).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_457_fin r
  change even22A457
    (-(33 * (46 * (80000000 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (80000000 + (r.val : ZMod 461)) + 29))) = true →
      (5582110045729757274639729678430547494345727900938718759463463611698749701021248022291549153832821198125814215275461313852529544839408123579).testBit r.val = true := by decide

theorem even22_b29_s5_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (80000000 + (i : ZMod 461)) + 29))) = true) :
    (5582110045729757274639729678430547494345727900938718759463463611698749701021248022291549153832821198125814215275461313852529544839408123579).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_461_fin r
  change even22A461
    (-(33 * (46 * (80000000 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (80000000 + (r.val : ZMod 463)) + 29))) = true →
      (23816867433912310938903665006904962381299803008528202252735488096850740584592305855398020456833279168970014532245718347920386581849964314095).testBit r.val = true := by decide

theorem even22_b29_s5_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (80000000 + (i : ZMod 463)) + 29))) = true) :
    (23816867433912310938903665006904962381299803008528202252735488096850740584592305855398020456833279168970014532245718347920386581849964314095).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_463_fin r
  change even22A463
    (-(33 * (46 * (80000000 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (80000000 + (r.val : ZMod 467)) + 29))) = true →
      (380874936354456155174036212749908263604566945470340041218539587240335042908897832814089758882846912410191128306699873074019795478929033133790).testBit r.val = true := by decide

theorem even22_b29_s5_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (80000000 + (i : ZMod 467)) + 29))) = true) :
    (380874936354456155174036212749908263604566945470340041218539587240335042908897832814089758882846912410191128306699873074019795478929033133790).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_467_fin r
  change even22A467
    (-(33 * (46 * (80000000 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (80000000 + (r.val : ZMod 479)) + 29))) = true →
      (1265078405214367386504299330218620953186265906948801621795351722300263712036226215283264251487493182411860586959579904206499649807318147382607741).testBit r.val = true := by decide

theorem even22_b29_s5_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (80000000 + (i : ZMod 479)) + 29))) = true) :
    (1265078405214367386504299330218620953186265906948801621795351722300263712036226215283264251487493182411860586959579904206499649807318147382607741).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_479_fin r
  change even22A479
    (-(33 * (46 * (80000000 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (80000000 + (r.val : ZMod 487)) + 29))) = true →
      (199590557818957722256319111881672184363120818392267071363665782802790382941979983838195955772958315843890826971238904781108882678630223280139664879).testBit r.val = true := by decide

theorem even22_b29_s5_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (80000000 + (i : ZMod 487)) + 29))) = true) :
    (199590557818957722256319111881672184363120818392267071363665782802790382941979983838195955772958315843890826971238904781108882678630223280139664879).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_487_fin r
  change even22A487
    (-(33 * (46 * (80000000 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (80000000 + (r.val : ZMod 491)) + 29))) = true →
      (5592947096405794746449489441334144952840576287853352387917579224318491885547578314631768954567550015412023950445290109707761473465828600323024879087).testBit r.val = true := by decide

theorem even22_b29_s5_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (80000000 + (i : ZMod 491)) + 29))) = true) :
    (5592947096405794746449489441334144952840576287853352387917579224318491885547578314631768954567550015412023950445290109707761473465828600323024879087).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_491_fin r
  change even22A491
    (-(33 * (46 * (80000000 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S5Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453574854397159281405606482237533488213390968334597453158191461000512875477847690554446519645173798679309709069334183088815245214318585) (.leaf 457 279106025418860054796041674008269497129122186053771946109952275952662141678518864200507001194526508902244504992268198771006731129152338943)) (.node (.leaf 461 5582110045729757274639729678430547494345727900938718759463463611698749701021248022291549153832821198125814215275461313852529544839408123579) (.leaf 463 23816867433912310938903665006904962381299803008528202252735488096850740584592305855398020456833279168970014532245718347920386581849964314095))) (.node (.node (.leaf 467 380874936354456155174036212749908263604566945470340041218539587240335042908897832814089758882846912410191128306699873074019795478929033133790) (.leaf 479 1265078405214367386504299330218620953186265906948801621795351722300263712036226215283264251487493182411860586959579904206499649807318147382607741)) (.node (.leaf 487 199590557818957722256319111881672184363120818392267071363665782802790382941979983838195955772958315843890826971238904781108882678630223280139664879) (.leaf 491 5592947096405794746449489441334144952840576287853352387917579224318491885547578314631768954567550015412023950445290109707761473465828600323024879087))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S5Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S5Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
