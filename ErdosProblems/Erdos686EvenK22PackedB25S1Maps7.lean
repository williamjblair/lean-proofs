import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s1_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (16000000 + (r.val : ZMod 449)) + 25))) = true →
      (1271967724085934787894018455430009167872931613302174490997976720322616249014075956299945362727386713477595292460321459260998340236476412).testBit r.val = true := by decide

theorem even22_b25_s1_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (16000000 + (i : ZMod 449)) + 25))) = true) :
    (1271967724085934787894018455430009167872931613302174490997976720322616249014075956299945362727386713477595292460321459260998340236476412).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_449_fin r
  change even22A449
    (-(33 * (46 * (16000000 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (16000000 + (r.val : ZMod 457)) + 25))) = true →
      (372135747020066723736434076458864025453377603356665826529825311205550378351723328837799251400844877775510870604867275322226714947571675103).testBit r.val = true := by decide

theorem even22_b25_s1_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (16000000 + (i : ZMod 457)) + 25))) = true) :
    (372135747020066723736434076458864025453377603356665826529825311205550378351723328837799251400844877775510870604867275322226714947571675103).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_457_fin r
  change even22A457
    (-(33 * (46 * (16000000 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (16000000 + (r.val : ZMod 461)) + 25))) = true →
      (5952717585950705949164520735482461136629185742779143097021331809019327387105669206759900596362872648374885863635441740450858344947755464703).testBit r.val = true := by decide

theorem even22_b25_s1_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (16000000 + (i : ZMod 461)) + 25))) = true) :
    (5952717585950705949164520735482461136629185742779143097021331809019327387105669206759900596362872648374885863635441740450858344947755464703).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_461_fin r
  change even22A461
    (-(33 * (46 * (16000000 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (16000000 + (r.val : ZMod 463)) + 25))) = true →
      (23816301144010671114429943781323136399904605436111769963222283706268219910768347041038684175748574362125504201578670879783143237501539033023).testBit r.val = true := by decide

theorem even22_b25_s1_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (16000000 + (i : ZMod 463)) + 25))) = true) :
    (23816301144010671114429943781323136399904605436111769963222283706268219910768347041038684175748574362125504201578670879783143237501539033023).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_463_fin r
  change even22A463
    (-(33 * (46 * (16000000 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (16000000 + (r.val : ZMod 467)) + 25))) = true →
      (355761003141902800480688619840549364462238190765906794296017721696877802478775511440350718260759273693801682973384500083060743043023300451839).testBit r.val = true := by decide

theorem even22_b25_s1_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (16000000 + (i : ZMod 467)) + 25))) = true) :
    (355761003141902800480688619840549364462238190765906794296017721696877802478775511440350718260759273693801682973384500083060743043023300451839).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_467_fin r
  change even22A467
    (-(33 * (46 * (16000000 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (16000000 + (r.val : ZMod 479)) + 25))) = true →
      (1560677778283747886567034206737001539559062614116390581673544777578494041091824889381337481435720284475423138219262070584927108020959208548597502).testBit r.val = true := by decide

theorem even22_b25_s1_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (16000000 + (i : ZMod 479)) + 25))) = true) :
    (1560677778283747886567034206737001539559062614116390581673544777578494041091824889381337481435720284475423138219262070584927108020959208548597502).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_479_fin r
  change even22A479
    (-(33 * (46 * (16000000 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (16000000 + (r.val : ZMod 487)) + 25))) = true →
      (196670110942766584944334802222211160426106449688887644560255665114327973431344959254927547373283113915517210465440318691473387584743451666458083319).testBit r.val = true := by decide

theorem even22_b25_s1_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (16000000 + (i : ZMod 487)) + 25))) = true) :
    (196670110942766584944334802222211160426106449688887644560255665114327973431344959254927547373283113915517210465440318691473387584743451666458083319).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_487_fin r
  change even22A487
    (-(33 * (46 * (16000000 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (16000000 + (r.val : ZMod 491)) + 25))) = true →
      (6187256774557434215065157983517116026951159717449208873949074559417611647825421741935174319688314079908752361906181921289838549662760187519060277183).testBit r.val = true := by decide

theorem even22_b25_s1_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (16000000 + (i : ZMod 491)) + 25))) = true) :
    (6187256774557434215065157983517116026951159717449208873949074559417611647825421741935174319688314079908752361906181921289838549662760187519060277183).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_491_fin r
  change even22A491
    (-(33 * (46 * (16000000 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S1Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1271967724085934787894018455430009167872931613302174490997976720322616249014075956299945362727386713477595292460321459260998340236476412) (.leaf 457 372135747020066723736434076458864025453377603356665826529825311205550378351723328837799251400844877775510870604867275322226714947571675103)) (.node (.leaf 461 5952717585950705949164520735482461136629185742779143097021331809019327387105669206759900596362872648374885863635441740450858344947755464703) (.leaf 463 23816301144010671114429943781323136399904605436111769963222283706268219910768347041038684175748574362125504201578670879783143237501539033023))) (.node (.node (.leaf 467 355761003141902800480688619840549364462238190765906794296017721696877802478775511440350718260759273693801682973384500083060743043023300451839) (.leaf 479 1560677778283747886567034206737001539559062614116390581673544777578494041091824889381337481435720284475423138219262070584927108020959208548597502)) (.node (.leaf 487 196670110942766584944334802222211160426106449688887644560255665114327973431344959254927547373283113915517210465440318691473387584743451666458083319) (.leaf 491 6187256774557434215065157983517116026951159717449208873949074559417611647825421741935174319688314079908752361906181921289838549662760187519060277183))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S1Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S1Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
