import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s4_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (64000000 + (r.val : ZMod 307)) + 25))) = true →
      (260740092106122921722897685365091769953258260398342091514840347134614989364894408842810228591).testBit r.val = true := by decide

theorem even22_b25_s4_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (64000000 + (i : ZMod 307)) + 25))) = true) :
    (260740092106122921722897685365091769953258260398342091514840347134614989364894408842810228591).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_307_fin r
  change even22A307
    (-(33 * (46 * (64000000 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (64000000 + (r.val : ZMod 311)) + 25))) = true →
      (4169804684806491523896404593341729065220767609770470364275940375284578890255805702302263672767).testBit r.val = true := by decide

theorem even22_b25_s4_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (64000000 + (i : ZMod 311)) + 25))) = true) :
    (4169804684806491523896404593341729065220767609770470364275940375284578890255805702302263672767).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_311_fin r
  change even22A311
    (-(33 * (46 * (64000000 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (64000000 + (r.val : ZMod 313)) + 25))) = true →
      (16638446181784455937117508596727856835000302264998052302074242773391051023030120665245233971199).testBit r.val = true := by decide

theorem even22_b25_s4_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (64000000 + (i : ZMod 313)) + 25))) = true) :
    (16638446181784455937117508596727856835000302264998052302074242773391051023030120665245233971199).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_313_fin r
  change even22A313
    (-(33 * (46 * (64000000 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (64000000 + (r.val : ZMod 317)) + 25))) = true →
      (266998371346443629750982376568546555600703747343578167681460290718212806941614603859013019428863).testBit r.val = true := by decide

theorem even22_b25_s4_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (64000000 + (i : ZMod 317)) + 25))) = true) :
    (266998371346443629750982376568546555600703747343578167681460290718212806941614603859013019428863).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_317_fin r
  change even22A317
    (-(33 * (46 * (64000000 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (64000000 + (r.val : ZMod 331)) + 25))) = true →
      (4235657077416065796335346967116244663961543530078771054289938053469053058846832630556272692704030555).testBit r.val = true := by decide

theorem even22_b25_s4_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (64000000 + (i : ZMod 331)) + 25))) = true) :
    (4235657077416065796335346967116244663961543530078771054289938053469053058846832630556272692704030555).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_331_fin r
  change even22A331
    (-(33 * (46 * (64000000 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (64000000 + (r.val : ZMod 337)) + 25))) = true →
      (133353672360555526527309254070297577697849890467675020045069682907411202464453263356107490913660436334).testBit r.val = true := by decide

theorem even22_b25_s4_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (64000000 + (i : ZMod 337)) + 25))) = true) :
    (133353672360555526527309254070297577697849890467675020045069682907411202464453263356107490913660436334).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_337_fin r
  change even22A337
    (-(33 * (46 * (64000000 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (64000000 + (r.val : ZMod 347)) + 25))) = true →
      (286687326865259684787394316989100764599024191522818781540010616770005530864291459946846435696827439120383).testBit r.val = true := by decide

theorem even22_b25_s4_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (64000000 + (i : ZMod 347)) + 25))) = true) :
    (286687326865259684787394316989100764599024191522818781540010616770005530864291459946846435696827439120383).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_347_fin r
  change even22A347
    (-(33 * (46 * (64000000 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (64000000 + (r.val : ZMod 349)) + 25))) = true →
      (1141118231004079313481966310411365085959517278135435968107251232084897914356198454228519935865202208143359).testBit r.val = true := by decide

theorem even22_b25_s4_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (64000000 + (i : ZMod 349)) + 25))) = true) :
    (1141118231004079313481966310411365085959517278135435968107251232084897914356198454228519935865202208143359).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_349_fin r
  change even22A349
    (-(33 * (46 * (64000000 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S4Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260740092106122921722897685365091769953258260398342091514840347134614989364894408842810228591) (.leaf 311 4169804684806491523896404593341729065220767609770470364275940375284578890255805702302263672767)) (.node (.leaf 313 16638446181784455937117508596727856835000302264998052302074242773391051023030120665245233971199) (.leaf 317 266998371346443629750982376568546555600703747343578167681460290718212806941614603859013019428863))) (.node (.node (.leaf 331 4235657077416065796335346967116244663961543530078771054289938053469053058846832630556272692704030555) (.leaf 337 133353672360555526527309254070297577697849890467675020045069682907411202464453263356107490913660436334)) (.node (.leaf 347 286687326865259684787394316989100764599024191522818781540010616770005530864291459946846435696827439120383) (.leaf 349 1141118231004079313481966310411365085959517278135435968107251232084897914356198454228519935865202208143359))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S4Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S4Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
