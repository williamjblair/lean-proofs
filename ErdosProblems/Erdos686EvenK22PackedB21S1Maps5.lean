import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (16000000 + (r.val : ZMod 353)) + 21))) = true →
      (17196652918309624022724312250559562411631883221875204639996370448447407745564581395671193639005282970894334).testBit r.val = true := by decide

theorem even22_b21_s1_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (16000000 + (i : ZMod 353)) + 21))) = true) :
    (17196652918309624022724312250559562411631883221875204639996370448447407745564581395671193639005282970894334).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_353_fin r
  change even22A353
    (-(33 * (46 * (16000000 + ((i % 353 : ℕ) : ZMod 353)) + 21))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (16000000 + (r.val : ZMod 359)) + 21))) = true →
      (577954887702625577001594287183429187345276559915643222655807563822647854503968730323248622561435951151667190).testBit r.val = true := by decide

theorem even22_b21_s1_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (16000000 + (i : ZMod 359)) + 21))) = true) :
    (577954887702625577001594287183429187345276559915643222655807563822647854503968730323248622561435951151667190).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_359_fin r
  change even22A359
    (-(33 * (46 * (16000000 + ((i % 359 : ℕ) : ZMod 359)) + 21))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (16000000 + (r.val : ZMod 367)) + 21))) = true →
      (300608862473497040937967204253986138952602109028453154804114028929863128417964961252376428799359270222678650623).testBit r.val = true := by decide

theorem even22_b21_s1_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (16000000 + (i : ZMod 367)) + 21))) = true) :
    (300608862473497040937967204253986138952602109028453154804114028929863128417964961252376428799359270222678650623).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_367_fin r
  change even22A367
    (-(33 * (46 * (16000000 + ((i % 367 : ℕ) : ZMod 367)) + 21))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (16000000 + (r.val : ZMod 373)) + 21))) = true →
      (18036807035143103004483536330403626448320216407715052356485384959312871403808157666063739882194670161684991049727).testBit r.val = true := by decide

theorem even22_b21_s1_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (16000000 + (i : ZMod 373)) + 21))) = true) :
    (18036807035143103004483536330403626448320216407715052356485384959312871403808157666063739882194670161684991049727).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_373_fin r
  change even22A373
    (-(33 * (46 * (16000000 + ((i % 373 : ℕ) : ZMod 373)) + 21))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (16000000 + (r.val : ZMod 379)) + 21))) = true →
      (1231312670621430535582846532239723562551186386389955447045868879234788192425392934270675416819643843379717593620471).testBit r.val = true := by decide

theorem even22_b21_s1_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (16000000 + (i : ZMod 379)) + 21))) = true) :
    (1231312670621430535582846532239723562551186386389955447045868879234788192425392934270675416819643843379717593620471).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_379_fin r
  change even22A379
    (-(33 * (46 * (16000000 + ((i % 379 : ℕ) : ZMod 379)) + 21))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (16000000 + (r.val : ZMod 383)) + 21))) = true →
      (19378068768631688224024110603222117995121704965980556541068131778310981782258661826049404721684938917883588724518911).testBit r.val = true := by decide

theorem even22_b21_s1_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (16000000 + (i : ZMod 383)) + 21))) = true) :
    (19378068768631688224024110603222117995121704965980556541068131778310981782258661826049404721684938917883588724518911).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_383_fin r
  change even22A383
    (-(33 * (46 * (16000000 + ((i % 383 : ℕ) : ZMod 383)) + 21))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (16000000 + (r.val : ZMod 389)) + 21))) = true →
      (1260229243952506745151841708494031503323815424099149508835230350407354680942140190991581668604910560949078465322155770).testBit r.val = true := by decide

theorem even22_b21_s1_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (16000000 + (i : ZMod 389)) + 21))) = true) :
    (1260229243952506745151841708494031503323815424099149508835230350407354680942140190991581668604910560949078465322155770).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_389_fin r
  change even22A389
    (-(33 * (46 * (16000000 + ((i % 389 : ℕ) : ZMod 389)) + 21))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (16000000 + (r.val : ZMod 397)) + 21))) = true →
      (322465707275757028026148166753924122373909527655715541547013372537892280991527212187190759555084915804568392355717045247).testBit r.val = true := by decide

theorem even22_b21_s1_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (16000000 + (i : ZMod 397)) + 21))) = true) :
    (322465707275757028026148166753924122373909527655715541547013372537892280991527212187190759555084915804568392355717045247).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_397_fin r
  change even22A397
    (-(33 * (46 * (16000000 + ((i % 397 : ℕ) : ZMod 397)) + 21))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 17196652918309624022724312250559562411631883221875204639996370448447407745564581395671193639005282970894334) (.leaf 359 577954887702625577001594287183429187345276559915643222655807563822647854503968730323248622561435951151667190)) (.node (.leaf 367 300608862473497040937967204253986138952602109028453154804114028929863128417964961252376428799359270222678650623) (.leaf 373 18036807035143103004483536330403626448320216407715052356485384959312871403808157666063739882194670161684991049727))) (.node (.node (.leaf 379 1231312670621430535582846532239723562551186386389955447045868879234788192425392934270675416819643843379717593620471) (.leaf 383 19378068768631688224024110603222117995121704965980556541068131778310981782258661826049404721684938917883588724518911)) (.node (.leaf 389 1260229243952506745151841708494031503323815424099149508835230350407354680942140190991581668604910560949078465322155770) (.leaf 397 322465707275757028026148166753924122373909527655715541547013372537892280991527212187190759555084915804568392355717045247))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
