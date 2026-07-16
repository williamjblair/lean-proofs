import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s5_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (80000000 + (r.val : ZMod 353)) + 29))) = true →
      (13474267185411046736988112077561377642067619900832573309262275726436751186743189042481042441390931999948795).testBit r.val = true := by decide

theorem even22_b29_s5_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (80000000 + (i : ZMod 353)) + 29))) = true) :
    (13474267185411046736988112077561377642067619900832573309262275726436751186743189042481042441390931999948795).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_353_fin r
  change even22A353
    (-(33 * (46 * (80000000 + ((i % 353 : ℕ) : ZMod 353)) + 29))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (80000000 + (r.val : ZMod 359)) + 29))) = true →
      (1164873276506319038762615614029897835634805271324441059839522297356411101055877389168354278430658122447968207).testBit r.val = true := by decide

theorem even22_b29_s5_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (80000000 + (i : ZMod 359)) + 29))) = true) :
    (1164873276506319038762615614029897835634805271324441059839522297356411101055877389168354278430658122447968207).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_359_fin r
  change even22A359
    (-(33 * (46 * (80000000 + ((i % 359 : ℕ) : ZMod 359)) + 29))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (80000000 + (r.val : ZMod 367)) + 29))) = true →
      (297934032761259501571830784185547157727626566721934019392301868451074455686488981151632789359158092211270188029).testBit r.val = true := by decide

theorem even22_b29_s5_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (80000000 + (i : ZMod 367)) + 29))) = true) :
    (297934032761259501571830784185547157727626566721934019392301868451074455686488981151632789359158092211270188029).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_367_fin r
  change even22A367
    (-(33 * (46 * (80000000 + ((i % 367 : ℕ) : ZMod 367)) + 29))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (80000000 + (r.val : ZMod 373)) + 29))) = true →
      (13226982073738686964153274900774418444663519197700223653869165588102050563423197632515334282540638959831777017791).testBit r.val = true := by decide

theorem even22_b29_s5_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (80000000 + (i : ZMod 373)) + 29))) = true) :
    (13226982073738686964153274900774418444663519197700223653869165588102050563423197632515334282540638959831777017791).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_373_fin r
  change even22A373
    (-(33 * (46 * (80000000 + ((i % 373 : ℕ) : ZMod 373)) + 29))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (80000000 + (r.val : ZMod 379)) + 29))) = true →
      (1212073432790267472486689190425288761706869444526596757985747108263863459393876468850405785972330467151475480903159).testBit r.val = true := by decide

theorem even22_b29_s5_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (80000000 + (i : ZMod 379)) + 29))) = true) :
    (1212073432790267472486689190425288761706869444526596757985747108263863459393876468850405785972330467151475480903159).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_379_fin r
  change even22A379
    (-(33 * (46 * (80000000 + ((i % 379 : ℕ) : ZMod 379)) + 29))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (80000000 + (r.val : ZMod 383)) + 29))) = true →
      (19699762989734581531720073665650873096123101452983575751796056727376917081215305053012381414181700663684250405362159).testBit r.val = true := by decide

theorem even22_b29_s5_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (80000000 + (i : ZMod 383)) + 29))) = true) :
    (19699762989734581531720073665650873096123101452983575751796056727376917081215305053012381414181700663684250405362159).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_383_fin r
  change even22A383
    (-(33 * (46 * (80000000 + ((i % 383 : ℕ) : ZMod 383)) + 29))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (80000000 + (r.val : ZMod 389)) + 29))) = true →
      (1255938947510074024857218610613364482059166448709641229056446793375219886558401749282948886557537802786580183285497855).testBit r.val = true := by decide

theorem even22_b29_s5_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (80000000 + (i : ZMod 389)) + 29))) = true) :
    (1255938947510074024857218610613364482059166448709641229056446793375219886558401749282948886557537802786580183285497855).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_389_fin r
  change even22A389
    (-(33 * (46 * (80000000 + ((i % 389 : ℕ) : ZMod 389)) + 29))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (80000000 + (r.val : ZMod 397)) + 29))) = true →
      (301346536175302126898352849105335451489520631364009191060160595510083451702581088479695861970097891670594031367921598463).testBit r.val = true := by decide

theorem even22_b29_s5_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (80000000 + (i : ZMod 397)) + 29))) = true) :
    (301346536175302126898352849105335451489520631364009191060160595510083451702581088479695861970097891670594031367921598463).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_397_fin r
  change even22A397
    (-(33 * (46 * (80000000 + ((i % 397 : ℕ) : ZMod 397)) + 29))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB29S5Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 13474267185411046736988112077561377642067619900832573309262275726436751186743189042481042441390931999948795) (.leaf 359 1164873276506319038762615614029897835634805271324441059839522297356411101055877389168354278430658122447968207)) (.node (.leaf 367 297934032761259501571830784185547157727626566721934019392301868451074455686488981151632789359158092211270188029) (.leaf 373 13226982073738686964153274900774418444663519197700223653869165588102050563423197632515334282540638959831777017791))) (.node (.node (.leaf 379 1212073432790267472486689190425288761706869444526596757985747108263863459393876468850405785972330467151475480903159) (.leaf 383 19699762989734581531720073665650873096123101452983575751796056727376917081215305053012381414181700663684250405362159)) (.node (.leaf 389 1255938947510074024857218610613364482059166448709641229056446793375219886558401749282948886557537802786580183285497855) (.leaf 397 301346536175302126898352849105335451489520631364009191060160595510083451702581088479695861970097891670594031367921598463))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S5Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S5Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
