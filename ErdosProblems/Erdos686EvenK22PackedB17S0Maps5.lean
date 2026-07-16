import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (0 + (r.val : ZMod 353)) + 17))) = true →
      (16914552284374205963937255608895865561610664320453027037758302413483052539671426488042845162694895491481583).testBit r.val = true := by decide

theorem even22_b17_s0_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (0 + (i : ZMod 353)) + 17))) = true) :
    (16914552284374205963937255608895865561610664320453027037758302413483052539671426488042845162694895491481583).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_353_fin r
  change even22A353
    (-(33 * (46 * (0 + ((i % 353 : ℕ) : ZMod 353)) + 17))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (0 + (r.val : ZMod 359)) + 17))) = true →
      (586517266133537320181620704866456614861091098883259830972599635932563998335601130200349607359016710331924206).testBit r.val = true := by decide

theorem even22_b17_s0_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (0 + (i : ZMod 359)) + 17))) = true) :
    (586517266133537320181620704866456614861091098883259830972599635932563998335601130200349607359016710331924206).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_359_fin r
  change even22A359
    (-(33 * (46 * (0 + ((i % 359 : ℕ) : ZMod 359)) + 17))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (0 + (r.val : ZMod 367)) + 17))) = true →
      (224138960931038062031995552559145313019903161769246964347816491533813855851587071055219227058572116453943541623).testBit r.val = true := by decide

theorem even22_b17_s0_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (0 + (i : ZMod 367)) + 17))) = true) :
    (224138960931038062031995552559145313019903161769246964347816491533813855851587071055219227058572116453943541623).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_367_fin r
  change even22A367
    (-(33 * (46 * (0 + ((i % 367 : ℕ) : ZMod 367)) + 17))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (0 + (r.val : ZMod 373)) + 17))) = true →
      (16824958919638713010683417297896623615392407680121882863220485319475253882179572998578404985652545714939871723257).testBit r.val = true := by decide

theorem even22_b17_s0_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (0 + (i : ZMod 373)) + 17))) = true) :
    (16824958919638713010683417297896623615392407680121882863220485319475253882179572998578404985652545714939871723257).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_373_fin r
  change even22A373
    (-(33 * (46 * (0 + ((i % 373 : ℕ) : ZMod 373)) + 17))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (0 + (r.val : ZMod 379)) + 17))) = true →
      (1226498034558169706436048603681439277412006445577267390623008565924941264640253810227645500713881220732203575541759).testBit r.val = true := by decide

theorem even22_b17_s0_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (0 + (i : ZMod 379)) + 17))) = true) :
    (1226498034558169706436048603681439277412006445577267390623008565924941264640253810227645500713881220732203575541759).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_379_fin r
  change even22A379
    (-(33 * (46 * (0 + ((i % 379 : ℕ) : ZMod 379)) + 17))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (0 + (r.val : ZMod 383)) + 17))) = true →
      (14467924113542619433104815387816338007687123599047767776874827491757174457728158886398480295817004879346976872722303).testBit r.val = true := by decide

theorem even22_b17_s0_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (0 + (i : ZMod 383)) + 17))) = true) :
    (14467924113542619433104815387816338007687123599047767776874827491757174457728158886398480295817004879346976872722303).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_383_fin r
  change even22A383
    (-(33 * (46 * (0 + ((i % 383 : ℕ) : ZMod 383)) + 17))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (0 + (r.val : ZMod 389)) + 17))) = true →
      (1254688395041854924192398158170400805895060081934259703908829951356199715912307221922255779221146991979518123721752311).testBit r.val = true := by decide

theorem even22_b17_s0_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (0 + (i : ZMod 389)) + 17))) = true) :
    (1254688395041854924192398158170400805895060081934259703908829951356199715912307221922255779221146991979518123721752311).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_389_fin r
  change even22A389
    (-(33 * (46 * (0 + ((i % 389 : ℕ) : ZMod 389)) + 17))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (0 + (r.val : ZMod 397)) + 17))) = true →
      (322150110048257626575440684722296834067197004884506938047154268800622994528654880143202160846709000626170482624059932653).testBit r.val = true := by decide

theorem even22_b17_s0_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (0 + (i : ZMod 397)) + 17))) = true) :
    (322150110048257626575440684722296834067197004884506938047154268800622994528654880143202160846709000626170482624059932653).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_397_fin r
  change even22A397
    (-(33 * (46 * (0 + ((i % 397 : ℕ) : ZMod 397)) + 17))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 16914552284374205963937255608895865561610664320453027037758302413483052539671426488042845162694895491481583) (.leaf 359 586517266133537320181620704866456614861091098883259830972599635932563998335601130200349607359016710331924206)) (.node (.leaf 367 224138960931038062031995552559145313019903161769246964347816491533813855851587071055219227058572116453943541623) (.leaf 373 16824958919638713010683417297896623615392407680121882863220485319475253882179572998578404985652545714939871723257))) (.node (.node (.leaf 379 1226498034558169706436048603681439277412006445577267390623008565924941264640253810227645500713881220732203575541759) (.leaf 383 14467924113542619433104815387816338007687123599047767776874827491757174457728158886398480295817004879346976872722303)) (.node (.leaf 389 1254688395041854924192398158170400805895060081934259703908829951356199715912307221922255779221146991979518123721752311) (.leaf 397 322150110048257626575440684722296834067197004884506938047154268800622994528654880143202160846709000626170482624059932653))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
