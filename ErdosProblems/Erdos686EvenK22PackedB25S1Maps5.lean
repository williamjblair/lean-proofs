import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s1_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (16000000 + (r.val : ZMod 353)) + 25))) = true →
      (18303159032526412272209835419777446152147848014387713659045161396647444835263867332309062145947416672534527).testBit r.val = true := by decide

theorem even22_b25_s1_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (16000000 + (i : ZMod 353)) + 25))) = true) :
    (18303159032526412272209835419777446152147848014387713659045161396647444835263867332309062145947416672534527).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_353_fin r
  change even22A353
    (-(33 * (46 * (16000000 + ((i % 353 : ℕ) : ZMod 353)) + 25))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (16000000 + (r.val : ZMod 359)) + 25))) = true →
      (1099150248352829131808604768861486814186299049463764502055921626373531451953216910421014594215038604599230335).testBit r.val = true := by decide

theorem even22_b25_s1_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (16000000 + (i : ZMod 359)) + 25))) = true) :
    (1099150248352829131808604768861486814186299049463764502055921626373531451953216910421014594215038604599230335).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_359_fin r
  change even22A359
    (-(33 * (46 * (16000000 + ((i % 359 : ℕ) : ZMod 359)) + 25))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (16000000 + (r.val : ZMod 367)) + 25))) = true →
      (279178107924721440385671658761131285292400969953617550984682237115736358989222683869588012320511979773547765743).testBit r.val = true := by decide

theorem even22_b25_s1_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (16000000 + (i : ZMod 367)) + 25))) = true) :
    (279178107924721440385671658761131285292400969953617550984682237115736358989222683869588012320511979773547765743).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_367_fin r
  change even22A367
    (-(33 * (46 * (16000000 + ((i % 367 : ℕ) : ZMod 367)) + 25))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (16000000 + (r.val : ZMod 373)) + 25))) = true →
      (4508027469715244351694255293349359067956749890097354905506826619783388776989805670929128397552571366272185380831).testBit r.val = true := by decide

theorem even22_b25_s1_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (16000000 + (i : ZMod 373)) + 25))) = true) :
    (4508027469715244351694255293349359067956749890097354905506826619783388776989805670929128397552571366272185380831).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_373_fin r
  change even22A373
    (-(33 * (46 * (16000000 + ((i % 373 : ℕ) : ZMod 373)) + 25))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (16000000 + (r.val : ZMod 379)) + 25))) = true →
      (1192777805792420600447354594672883575079053642292015086460946151298129040864541061896856133414952751380669227072511).testBit r.val = true := by decide

theorem even22_b25_s1_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (16000000 + (i : ZMod 379)) + 25))) = true) :
    (1192777805792420600447354594672883575079053642292015086460946151298129040864541061896856133414952751380669227072511).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_379_fin r
  change even22A379
    (-(33 * (46 * (16000000 + ((i % 379 : ℕ) : ZMod 379)) + 25))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (16000000 + (r.val : ZMod 383)) + 25))) = true →
      (19700993704026768526742489917554639192948019567709287426790404592861675543419482750777060897413636697406362323222459).testBit r.val = true := by decide

theorem even22_b25_s1_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (16000000 + (i : ZMod 383)) + 25))) = true) :
    (19700993704026768526742489917554639192948019567709287426790404592861675543419482750777060897413636697406362323222459).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_383_fin r
  change even22A383
    (-(33 * (46 * (16000000 + ((i % 383 : ℕ) : ZMod 383)) + 25))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (16000000 + (r.val : ZMod 389)) + 25))) = true →
      (1258353469900936362693849421521771621173574112109762738539176601845174095401203506337907386652499931257066568875506815).testBit r.val = true := by decide

theorem even22_b25_s1_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (16000000 + (i : ZMod 389)) + 25))) = true) :
    (1258353469900936362693849421521771621173574112109762738539176601845174095401203506337907386652499931257066568875506815).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_389_fin r
  change even22A389
    (-(33 * (46 * (16000000 + ((i % 389 : ℕ) : ZMod 389)) + 25))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (16000000 + (r.val : ZMod 397)) + 25))) = true →
      (299322264109541375662721450924416389208723424275202466730918163893925272029190341252230446553032242193980339846979254271).testBit r.val = true := by decide

theorem even22_b25_s1_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (16000000 + (i : ZMod 397)) + 25))) = true) :
    (299322264109541375662721450924416389208723424275202466730918163893925272029190341252230446553032242193980339846979254271).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_397_fin r
  change even22A397
    (-(33 * (46 * (16000000 + ((i % 397 : ℕ) : ZMod 397)) + 25))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB25S1Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18303159032526412272209835419777446152147848014387713659045161396647444835263867332309062145947416672534527) (.leaf 359 1099150248352829131808604768861486814186299049463764502055921626373531451953216910421014594215038604599230335)) (.node (.leaf 367 279178107924721440385671658761131285292400969953617550984682237115736358989222683869588012320511979773547765743) (.leaf 373 4508027469715244351694255293349359067956749890097354905506826619783388776989805670929128397552571366272185380831))) (.node (.node (.leaf 379 1192777805792420600447354594672883575079053642292015086460946151298129040864541061896856133414952751380669227072511) (.leaf 383 19700993704026768526742489917554639192948019567709287426790404592861675543419482750777060897413636697406362323222459)) (.node (.leaf 389 1258353469900936362693849421521771621173574112109762738539176601845174095401203506337907386652499931257066568875506815) (.leaf 397 299322264109541375662721450924416389208723424275202466730918163893925272029190341252230446553032242193980339846979254271))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S1Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S1Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
