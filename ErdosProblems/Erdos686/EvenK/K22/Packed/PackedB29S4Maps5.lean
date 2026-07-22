import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s4_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (64000000 + (r.val : ZMod 353)) + 29))) = true →
      (9165035484657566080815201762223244072582394842150302601166417487335987358469448824522132235220777491224303).testBit r.val = true := by decide

theorem even22_b29_s4_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (64000000 + (i : ZMod 353)) + 29))) = true) :
    (9165035484657566080815201762223244072582394842150302601166417487335987358469448824522132235220777491224303).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_353_fin r
  change even22A353
    (-(33 * (46 * (64000000 + ((i % 353 : ℕ) : ZMod 353)) + 29))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (64000000 + (r.val : ZMod 359)) + 29))) = true →
      (878407730178387185032193878510067614756394901166671085834884306587419064054871719723647482620180494708244283).testBit r.val = true := by decide

theorem even22_b29_s4_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (64000000 + (i : ZMod 359)) + 29))) = true) :
    (878407730178387185032193878510067614756394901166671085834884306587419064054871719723647482620180494708244283).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_359_fin r
  change even22A359
    (-(33 * (46 * (64000000 + ((i % 359 : ℕ) : ZMod 359)) + 29))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (64000000 + (r.val : ZMod 367)) + 29))) = true →
      (131517524563476593154961176947163130862339600305230942223279513463203277277267542129660712517293643022920054767).testBit r.val = true := by decide

theorem even22_b29_s4_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (64000000 + (i : ZMod 367)) + 29))) = true) :
    (131517524563476593154961176947163130862339600305230942223279513463203277277267542129660712517293643022920054767).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_367_fin r
  change even22A367
    (-(33 * (46 * (64000000 + ((i % 367 : ℕ) : ZMod 367)) + 29))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (64000000 + (r.val : ZMod 373)) + 29))) = true →
      (19239260658616995346524507047508409039556440258525949303435242660460524899102147422856255785290087386495947112415).testBit r.val = true := by decide

theorem even22_b29_s4_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (64000000 + (i : ZMod 373)) + 29))) = true) :
    (19239260658616995346524507047508409039556440258525949303435242660460524899102147422856255785290087386495947112415).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_373_fin r
  change even22A373
    (-(33 * (46 * (64000000 + ((i % 373 : ℕ) : ZMod 373)) + 29))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (64000000 + (r.val : ZMod 379)) + 29))) = true →
      (913864853109615419023206576961810041995047454486554463344215964560984414723347625479070640156928273947633603575551).testBit r.val = true := by decide

theorem even22_b29_s4_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (64000000 + (i : ZMod 379)) + 29))) = true) :
    (913864853109615419023206576961810041995047454486554463344215964560984414723347625479070640156928273947633603575551).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_379_fin r
  change even22A379
    (-(33 * (46 * (64000000 + ((i % 379 : ℕ) : ZMod 379)) + 29))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (64000000 + (r.val : ZMod 383)) + 29))) = true →
      (19662486375972269590752523843710798806948068504587758756952963227779380845631098702400850192628008158738079348125695).testBit r.val = true := by decide

theorem even22_b29_s4_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (64000000 + (i : ZMod 383)) + 29))) = true) :
    (19662486375972269590752523843710798806948068504587758756952963227779380845631098702400850192628008158738079348125695).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_383_fin r
  change even22A383
    (-(33 * (46 * (64000000 + ((i % 383 : ℕ) : ZMod 383)) + 29))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (64000000 + (r.val : ZMod 389)) + 29))) = true →
      (1260864123131260677281129461030603316558445072565164281976003290434704832835346779840282898762532862084573730818752511).testBit r.val = true := by decide

theorem even22_b29_s4_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (64000000 + (i : ZMod 389)) + 29))) = true) :
    (1260864123131260677281129461030603316558445072565164281976003290434704832835346779840282898762532862084573730818752511).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_389_fin r
  change even22A389
    (-(33 * (46 * (64000000 + ((i % 389 : ℕ) : ZMod 389)) + 29))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (64000000 + (r.val : ZMod 397)) + 29))) = true →
      (317106729535855614455176061198828772994859850809624717516990953060761211435931962847160546549476586010509283654004359167).testBit r.val = true := by decide

theorem even22_b29_s4_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (64000000 + (i : ZMod 397)) + 29))) = true) :
    (317106729535855614455176061198828772994859850809624717516990953060761211435931962847160546549476586010509283654004359167).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_397_fin r
  change even22A397
    (-(33 * (46 * (64000000 + ((i % 397 : ℕ) : ZMod 397)) + 29))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB29S4Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 9165035484657566080815201762223244072582394842150302601166417487335987358469448824522132235220777491224303) (.leaf 359 878407730178387185032193878510067614756394901166671085834884306587419064054871719723647482620180494708244283)) (.node (.leaf 367 131517524563476593154961176947163130862339600305230942223279513463203277277267542129660712517293643022920054767) (.leaf 373 19239260658616995346524507047508409039556440258525949303435242660460524899102147422856255785290087386495947112415))) (.node (.node (.leaf 379 913864853109615419023206576961810041995047454486554463344215964560984414723347625479070640156928273947633603575551) (.leaf 383 19662486375972269590752523843710798806948068504587758756952963227779380845631098702400850192628008158738079348125695)) (.node (.leaf 389 1260864123131260677281129461030603316558445072565164281976003290434704832835346779840282898762532862084573730818752511) (.leaf 397 317106729535855614455176061198828772994859850809624717516990953060761211435931962847160546549476586010509283654004359167))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S4Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S4Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
