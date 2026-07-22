import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s2_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (32000000 + (r.val : ZMod 449)) + 29))) = true →
      (718320736385113743446615796743924978785361749310375150256270073860306987233474551376801634332828120356118775632953959949699819468980223).testBit r.val = true := by decide

theorem even22_b29_s2_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (32000000 + (i : ZMod 449)) + 29))) = true) :
    (718320736385113743446615796743924978785361749310375150256270073860306987233474551376801634332828120356118775632953959949699819468980223).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_449_fin r
  change even22A449
    (-(33 * (46 * (32000000 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (32000000 + (r.val : ZMod 457)) + 29))) = true →
      (372073285535638971437020014496011492167646237362459267949099360272492960947688302139680315357088513071327098108159052067853766373830163951).testBit r.val = true := by decide

theorem even22_b29_s2_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (32000000 + (i : ZMod 457)) + 29))) = true) :
    (372073285535638971437020014496011492167646237362459267949099360272492960947688302139680315357088513071327098108159052067853766373830163951).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_457_fin r
  change even22A457
    (-(33 * (46 * (32000000 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (32000000 + (r.val : ZMod 461)) + 29))) = true →
      (5942597919668617300684171070374763051975513698827055556325779420025949873414760064491026446051323661485617388988567755948491088991948636159).testBit r.val = true := by decide

theorem even22_b29_s2_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (32000000 + (i : ZMod 461)) + 29))) = true) :
    (5942597919668617300684171070374763051975513698827055556325779420025949873414760064491026446051323661485617388988567755948491088991948636159).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_461_fin r
  change even22A461
    (-(33 * (46 * (32000000 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (32000000 + (r.val : ZMod 463)) + 29))) = true →
      (23069767397054905889063841264128801623337206177813326786400465198965034193661495705232646449307789881406498608631391757775965541943568095991).testBit r.val = true := by decide

theorem even22_b29_s2_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (32000000 + (i : ZMod 463)) + 29))) = true) :
    (23069767397054905889063841264128801623337206177813326786400465198965034193661495705232646449307789881406498608631391757775965541943568095991).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_463_fin r
  change even22A463
    (-(33 * (46 * (32000000 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (32000000 + (r.val : ZMod 467)) + 29))) = true →
      (355743575766371050140448460222282941184254814894378356219465630319728039672179226775516413190954680181364047687507796517985510945451646377471).testBit r.val = true := by decide

theorem even22_b29_s2_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (32000000 + (i : ZMod 467)) + 29))) = true) :
    (355743575766371050140448460222282941184254814894378356219465630319728039672179226775516413190954680181364047687507796517985510945451646377471).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_467_fin r
  change even22A467
    (-(33 * (46 * (32000000 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (32000000 + (r.val : ZMod 479)) + 29))) = true →
      (1458649995704052044840447964788928956542540406701769158042525196603825553986996110622475951867921039172845299666080681931737473365235393912635363).testBit r.val = true := by decide

theorem even22_b29_s2_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (32000000 + (i : ZMod 479)) + 29))) = true) :
    (1458649995704052044840447964788928956542540406701769158042525196603825553986996110622475951867921039172845299666080681931737473365235393912635363).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_479_fin r
  change even22A479
    (-(33 * (46 * (32000000 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (32000000 + (r.val : ZMod 487)) + 29))) = true →
      (344854844387183053972598818065336747066628948739569086060907739160632484813551729916011285456559683848834679194794804234236419256892388014265728735).testBit r.val = true := by decide

theorem even22_b29_s2_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (32000000 + (i : ZMod 487)) + 29))) = true) :
    (344854844387183053972598818065336747066628948739569086060907739160632484813551729916011285456559683848834679194794804234236419256892388014265728735).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_487_fin r
  change even22A487
    (-(33 * (46 * (32000000 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (32000000 + (r.val : ZMod 491)) + 29))) = true →
      (5553364688117403095434677064364518306027543231627948297190801916041599433641010581270784700645623920298742999392433410163841904054813208001483108343).testBit r.val = true := by decide

theorem even22_b29_s2_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (32000000 + (i : ZMod 491)) + 29))) = true) :
    (5553364688117403095434677064364518306027543231627948297190801916041599433641010581270784700645623920298742999392433410163841904054813208001483108343).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_491_fin r
  change even22A491
    (-(33 * (46 * (32000000 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S2Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 718320736385113743446615796743924978785361749310375150256270073860306987233474551376801634332828120356118775632953959949699819468980223) (.leaf 457 372073285535638971437020014496011492167646237362459267949099360272492960947688302139680315357088513071327098108159052067853766373830163951)) (.node (.leaf 461 5942597919668617300684171070374763051975513698827055556325779420025949873414760064491026446051323661485617388988567755948491088991948636159) (.leaf 463 23069767397054905889063841264128801623337206177813326786400465198965034193661495705232646449307789881406498608631391757775965541943568095991))) (.node (.node (.leaf 467 355743575766371050140448460222282941184254814894378356219465630319728039672179226775516413190954680181364047687507796517985510945451646377471) (.leaf 479 1458649995704052044840447964788928956542540406701769158042525196603825553986996110622475951867921039172845299666080681931737473365235393912635363)) (.node (.leaf 487 344854844387183053972598818065336747066628948739569086060907739160632484813551729916011285456559683848834679194794804234236419256892388014265728735) (.leaf 491 5553364688117403095434677064364518306027543231627948297190801916041599433641010581270784700645623920298742999392433410163841904054813208001483108343))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S2Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S2Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
