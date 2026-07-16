import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (0 + (r.val : ZMod 353)) + 29))) = true →
      (17774539906828953840776382257622769284248923910553347848609105867891669650344626245168491372201999907946455).testBit r.val = true := by decide

theorem even22_b29_s0_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (0 + (i : ZMod 353)) + 29))) = true) :
    (17774539906828953840776382257622769284248923910553347848609105867891669650344626245168491372201999907946455).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_353_fin r
  change even22A353
    (-(33 * (46 * (0 + ((i % 353 : ℕ) : ZMod 353)) + 29))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (0 + (r.val : ZMod 359)) + 29))) = true →
      (548128233765675526623217745967152421268273672609078963060155999740528010194811100014865374491959822141799422).testBit r.val = true := by decide

theorem even22_b29_s0_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (0 + (i : ZMod 359)) + 29))) = true) :
    (548128233765675526623217745967152421268273672609078963060155999740528010194811100014865374491959822141799422).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_359_fin r
  change even22A359
    (-(33 * (46 * (0 + ((i % 359 : ℕ) : ZMod 359)) + 29))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (0 + (r.val : ZMod 367)) + 29))) = true →
      (280649682618220400608392146882412978969933423944168055274257419351424198828486897725634127787167908373614033789).testBit r.val = true := by decide

theorem even22_b29_s0_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (0 + (i : ZMod 367)) + 29))) = true) :
    (280649682618220400608392146882412978969933423944168055274257419351424198828486897725634127787167908373614033789).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_367_fin r
  change even22A367
    (-(33 * (46 * (0 + ((i % 367 : ℕ) : ZMod 367)) + 29))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (0 + (r.val : ZMod 373)) + 29))) = true →
      (11986594382699069295809755910217083817508162493681064151432033984755094513710583184377827668539014087015451851771).testBit r.val = true := by decide

theorem even22_b29_s0_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (0 + (i : ZMod 373)) + 29))) = true) :
    (11986594382699069295809755910217083817508162493681064151432033984755094513710583184377827668539014087015451851771).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_373_fin r
  change even22A373
    (-(33 * (46 * (0 + ((i % 373 : ℕ) : ZMod 373)) + 29))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (0 + (r.val : ZMod 379)) + 29))) = true →
      (1231312325382976438569744468893258029687854399208609027133139534516428998416969474230369362136997287447374627471231).testBit r.val = true := by decide

theorem even22_b29_s0_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (0 + (i : ZMod 379)) + 29))) = true) :
    (1231312325382976438569744468893258029687854399208609027133139534516428998416969474230369362136997287447374627471231).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_379_fin r
  change even22A379
    (-(33 * (46 * (0 + ((i % 379 : ℕ) : ZMod 379)) + 29))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (0 + (r.val : ZMod 383)) + 29))) = true →
      (19621641137615953233935870506502195804813899589993399777557712343542525904304604972996828228575490026217819284176861).testBit r.val = true := by decide

theorem even22_b29_s0_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (0 + (i : ZMod 383)) + 29))) = true) :
    (19621641137615953233935870506502195804813899589993399777557712343542525904304604972996828228575490026217819284176861).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_383_fin r
  change even22A383
    (-(33 * (46 * (0 + ((i % 383 : ℕ) : ZMod 383)) + 29))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (0 + (r.val : ZMod 389)) + 29))) = true →
      (1179590043773699860733719720252385921604313889519561872367620457286785881229280522134875521576254637243907408629038463).testBit r.val = true := by decide

theorem even22_b29_s0_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (0 + (i : ZMod 389)) + 29))) = true) :
    (1179590043773699860733719720252385921604313889519561872367620457286785881229280522134875521576254637243907408629038463).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_389_fin r
  change even22A389
    (-(33 * (46 * (0 + ((i % 389 : ℕ) : ZMod 389)) + 29))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (0 + (r.val : ZMod 397)) + 29))) = true →
      (231999002855236016278117224140842300587913102734154848766354502154804593217340695161515332188327662458318298913074577151).testBit r.val = true := by decide

theorem even22_b29_s0_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (0 + (i : ZMod 397)) + 29))) = true) :
    (231999002855236016278117224140842300587913102734154848766354502154804593217340695161515332188327662458318298913074577151).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_397_fin r
  change even22A397
    (-(33 * (46 * (0 + ((i % 397 : ℕ) : ZMod 397)) + 29))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 17774539906828953840776382257622769284248923910553347848609105867891669650344626245168491372201999907946455) (.leaf 359 548128233765675526623217745967152421268273672609078963060155999740528010194811100014865374491959822141799422)) (.node (.leaf 367 280649682618220400608392146882412978969933423944168055274257419351424198828486897725634127787167908373614033789) (.leaf 373 11986594382699069295809755910217083817508162493681064151432033984755094513710583184377827668539014087015451851771))) (.node (.node (.leaf 379 1231312325382976438569744468893258029687854399208609027133139534516428998416969474230369362136997287447374627471231) (.leaf 383 19621641137615953233935870506502195804813899589993399777557712343542525904304604972996828228575490026217819284176861)) (.node (.leaf 389 1179590043773699860733719720252385921604313889519561872367620457286785881229280522134875521576254637243907408629038463) (.leaf 397 231999002855236016278117224140842300587913102734154848766354502154804593217340695161515332188327662458318298913074577151))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
