import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (0 + (r.val : ZMod 449)) + 25))) = true →
      (1453677421514030710786577855711843200695621061807142781438060814414591603291558978343143109023722877821205442439266077047744284230418303).testBit r.val = true := by decide

theorem even22_b25_s0_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (0 + (i : ZMod 449)) + 25))) = true) :
    (1453677421514030710786577855711843200695621061807142781438060814414591603291558978343143109023722877821205442439266077047744284230418303).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_449_fin r
  change even22A449
    (-(33 * (46 * (0 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (0 + (r.val : ZMod 457)) + 25))) = true →
      (369222626361628651723964719045930903720953909466957614371063122898977176302585005897880914333416574541992572755932242121782778972222750687).testBit r.val = true := by decide

theorem even22_b25_s0_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (0 + (i : ZMod 457)) + 25))) = true) :
    (369222626361628651723964719045930903720953909466957614371063122898977176302585005897880914333416574541992572755932242121782778972222750687).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_457_fin r
  change even22A457
    (-(33 * (46 * (0 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (0 + (r.val : ZMod 461)) + 25))) = true →
      (4462765633857807698727798874265226434031144765242551513549666214197560076367577632525188253619820885818928491536943644316596486667724390399).testBit r.val = true := by decide

theorem even22_b25_s0_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (0 + (i : ZMod 461)) + 25))) = true) :
    (4462765633857807698727798874265226434031144765242551513549666214197560076367577632525188253619820885818928491536943644316596486667724390399).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_461_fin r
  change even22A461
    (-(33 * (46 * (0 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (0 + (r.val : ZMod 463)) + 25))) = true →
      (21769523205080210966785909297658754118502206838504767951554659656199589612084465127756247793742963509337002594172770499024406747424832355831).testBit r.val = true := by decide

theorem even22_b25_s0_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (0 + (i : ZMod 463)) + 25))) = true) :
    (21769523205080210966785909297658754118502206838504767951554659656199589612084465127756247793742963509337002594172770499024406747424832355831).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_463_fin r
  change even22A463
    (-(33 * (46 * (0 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (0 + (r.val : ZMod 467)) + 25))) = true →
      (379514109311554494494163528812174561695474919579201003113582488502177671559279631743307819357642952990111310350390889957001845703722476689898).testBit r.val = true := by decide

theorem even22_b25_s0_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (0 + (i : ZMod 467)) + 25))) = true) :
    (379514109311554494494163528812174561695474919579201003113582488502177671559279631743307819357642952990111310350390889957001845703722476689898).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_467_fin r
  change even22A467
    (-(33 * (46 * (0 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (0 + (r.val : ZMod 479)) + 25))) = true →
      (1560850455187965215291734325146082133898280041360864948285762598454475121494658281791032389406172872441883481581734655462400846771246415149236093).testBit r.val = true := by decide

theorem even22_b25_s0_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (0 + (i : ZMod 479)) + 25))) = true) :
    (1560850455187965215291734325146082133898280041360864948285762598454475121494658281791032389406172872441883481581734655462400846771246415149236093).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_479_fin r
  change even22A479
    (-(33 * (46 * (0 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (0 + (r.val : ZMod 487)) + 25))) = true →
      (296468557637719626919326858474481028649629780036652079567051448268443297283006933504205566931084973640097668576652685031227615355849554313790086911).testBit r.val = true := by decide

theorem even22_b25_s0_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (0 + (i : ZMod 487)) + 25))) = true) :
    (296468557637719626919326858474481028649629780036652079567051448268443297283006933504205566931084973640097668576652685031227615355849554313790086911).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_487_fin r
  change even22A487
    (-(33 * (46 * (0 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (0 + (r.val : ZMod 491)) + 25))) = true →
      (5793934345731111974153042217187218761575538143920075193778450428875845174590260139036288116403576237505916062296843340069917168496092673337333905175).testBit r.val = true := by decide

theorem even22_b25_s0_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (0 + (i : ZMod 491)) + 25))) = true) :
    (5793934345731111974153042217187218761575538143920075193778450428875845174590260139036288116403576237505916062296843340069917168496092673337333905175).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_491_fin r
  change even22A491
    (-(33 * (46 * (0 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453677421514030710786577855711843200695621061807142781438060814414591603291558978343143109023722877821205442439266077047744284230418303) (.leaf 457 369222626361628651723964719045930903720953909466957614371063122898977176302585005897880914333416574541992572755932242121782778972222750687)) (.node (.leaf 461 4462765633857807698727798874265226434031144765242551513549666214197560076367577632525188253619820885818928491536943644316596486667724390399) (.leaf 463 21769523205080210966785909297658754118502206838504767951554659656199589612084465127756247793742963509337002594172770499024406747424832355831))) (.node (.node (.leaf 467 379514109311554494494163528812174561695474919579201003113582488502177671559279631743307819357642952990111310350390889957001845703722476689898) (.leaf 479 1560850455187965215291734325146082133898280041360864948285762598454475121494658281791032389406172872441883481581734655462400846771246415149236093)) (.node (.leaf 487 296468557637719626919326858474481028649629780036652079567051448268443297283006933504205566931084973640097668576652685031227615355849554313790086911) (.leaf 491 5793934345731111974153042217187218761575538143920075193778450428875845174590260139036288116403576237505916062296843340069917168496092673337333905175))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
