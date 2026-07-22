import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s1_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (16000000 + (r.val : ZMod 353)) + 17))) = true →
      (18034284098980738138709056263706237027284338379819461827309829939223956690333278982753942127255501739524014).testBit r.val = true := by decide

theorem even22_b17_s1_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (16000000 + (i : ZMod 353)) + 17))) = true) :
    (18034284098980738138709056263706237027284338379819461827309829939223956690333278982753942127255501739524014).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_353_fin r
  change even22A353
    (-(33 * (46 * (16000000 + ((i % 353 : ℕ) : ZMod 353)) + 17))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (16000000 + (r.val : ZMod 359)) + 17))) = true →
      (1100879326925964427934216101428425761113402206364887679321280575488084968798278874578985809655976587607669951).testBit r.val = true := by decide

theorem even22_b17_s1_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (16000000 + (i : ZMod 359)) + 17))) = true) :
    (1100879326925964427934216101428425761113402206364887679321280575488084968798278874578985809655976587607669951).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_359_fin r
  change even22A359
    (-(33 * (46 * (16000000 + ((i % 359 : ℕ) : ZMod 359)) + 17))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (16000000 + (r.val : ZMod 367)) + 17))) = true →
      (281504020108849964397476457694384767402341336084203375044003480217959717392734967444588158585956957072601841647).testBit r.val = true := by decide

theorem even22_b17_s1_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (16000000 + (i : ZMod 367)) + 17))) = true) :
    (281504020108849964397476457694384767402341336084203375044003480217959717392734967444588158585956957072601841647).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_367_fin r
  change even22A367
    (-(33 * (46 * (16000000 + ((i % 367 : ℕ) : ZMod 367)) + 17))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (16000000 + (r.val : ZMod 373)) + 17))) = true →
      (19201683580933381356651970493511358348337199035572038776762388118928361250240060393823232251337228959429611220447).testBit r.val = true := by decide

theorem even22_b17_s1_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (16000000 + (i : ZMod 373)) + 17))) = true) :
    (19201683580933381356651970493511358348337199035572038776762388118928361250240060393823232251337228959429611220447).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_373_fin r
  change even22A373
    (-(33 * (46 * (16000000 + ((i % 373 : ℕ) : ZMod 373)) + 17))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (16000000 + (r.val : ZMod 379)) + 17))) = true →
      (913714289515833476606112276632393690202335081235995286944031238770169324445906378407807538617353175689228044992446).testBit r.val = true := by decide

theorem even22_b17_s1_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (16000000 + (i : ZMod 379)) + 17))) = true) :
    (913714289515833476606112276632393690202335081235995286944031238770169324445906378407807538617353175689228044992446).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_379_fin r
  change even22A379
    (-(33 * (46 * (16000000 + ((i % 379 : ℕ) : ZMod 379)) + 17))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (16000000 + (r.val : ZMod 383)) + 17))) = true →
      (19690171601296235984135700818480277602239121777103366779506749726116998400087980507436439923570860993814661927271871).testBit r.val = true := by decide

theorem even22_b17_s1_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (16000000 + (i : ZMod 383)) + 17))) = true) :
    (19690171601296235984135700818480277602239121777103366779506749726116998400087980507436439923570860993814661927271871).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_383_fin r
  change even22A383
    (-(33 * (46 * (16000000 + ((i % 383 : ℕ) : ZMod 383)) + 17))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (16000000 + (r.val : ZMod 389)) + 17))) = true →
      (1253167065884125994495669511645154556055487449297518545194811050047758848452676902162044304489091953699010860979453885).testBit r.val = true := by decide

theorem even22_b17_s1_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (16000000 + (i : ZMod 389)) + 17))) = true) :
    (1253167065884125994495669511645154556055487449297518545194811050047758848452676902162044304489091953699010860979453885).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_389_fin r
  change even22A389
    (-(33 * (46 * (16000000 + ((i % 389 : ℕ) : ZMod 389)) + 17))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (16000000 + (r.val : ZMod 397)) + 17))) = true →
      (322773846884665053737966326003959827160497497756854801444489115285644665182616994294648609563787443027346966504984805307).testBit r.val = true := by decide

theorem even22_b17_s1_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (16000000 + (i : ZMod 397)) + 17))) = true) :
    (322773846884665053737966326003959827160497497756854801444489115285644665182616994294648609563787443027346966504984805307).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_397_fin r
  change even22A397
    (-(33 * (46 * (16000000 + ((i % 397 : ℕ) : ZMod 397)) + 17))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB17S1Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18034284098980738138709056263706237027284338379819461827309829939223956690333278982753942127255501739524014) (.leaf 359 1100879326925964427934216101428425761113402206364887679321280575488084968798278874578985809655976587607669951)) (.node (.leaf 367 281504020108849964397476457694384767402341336084203375044003480217959717392734967444588158585956957072601841647) (.leaf 373 19201683580933381356651970493511358348337199035572038776762388118928361250240060393823232251337228959429611220447))) (.node (.node (.leaf 379 913714289515833476606112276632393690202335081235995286944031238770169324445906378407807538617353175689228044992446) (.leaf 383 19690171601296235984135700818480277602239121777103366779506749726116998400087980507436439923570860993814661927271871)) (.node (.leaf 389 1253167065884125994495669511645154556055487449297518545194811050047758848452676902162044304489091953699010860979453885) (.leaf 397 322773846884665053737966326003959827160497497756854801444489115285644665182616994294648609563787443027346966504984805307))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S1Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S1Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
