import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (0 + (r.val : ZMod 307)) + 25))) = true →
      (193518404153091962340478508591038074808937179439539720569680450257634351560862575820365889535).testBit r.val = true := by decide

theorem even22_b25_s0_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (0 + (i : ZMod 307)) + 25))) = true) :
    (193518404153091962340478508591038074808937179439539720569680450257634351560862575820365889535).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_307_fin r
  change even22A307
    (-(33 * (46 * (0 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (0 + (r.val : ZMod 311)) + 25))) = true →
      (3910981759326128018703894861736621093517822681065773084350243907779465035062689970113954709501).testBit r.val = true := by decide

theorem even22_b25_s0_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (0 + (i : ZMod 311)) + 25))) = true) :
    (3910981759326128018703894861736621093517822681065773084350243907779465035062689970113954709501).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_311_fin r
  change even22A311
    (-(33 * (46 * (0 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (0 + (r.val : ZMod 313)) + 25))) = true →
      (16165917508190481493669212236072140220745806891590275650230411133261026952999586111980876857087).testBit r.val = true := by decide

theorem even22_b25_s0_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (0 + (i : ZMod 313)) + 25))) = true) :
    (16165917508190481493669212236072140220745806891590275650230411133261026952999586111980876857087).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_313_fin r
  change even22A313
    (-(33 * (46 * (0 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (0 + (r.val : ZMod 317)) + 25))) = true →
      (118310969933784382387167108800242568599454246706396644566256344288113932900734600431458045657086).testBit r.val = true := by decide

theorem even22_b25_s0_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (0 + (i : ZMod 317)) + 25))) = true) :
    (118310969933784382387167108800242568599454246706396644566256344288113932900734600431458045657086).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_317_fin r
  change even22A317
    (-(33 * (46 * (0 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (0 + (r.val : ZMod 331)) + 25))) = true →
      (2592019158922691962767660400660528472567166557246903865028191220453678933189516797329685358430747597).testBit r.val = true := by decide

theorem even22_b25_s0_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (0 + (i : ZMod 331)) + 25))) = true) :
    (2592019158922691962767660400660528472567166557246903865028191220453678933189516797329685358430747597).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_331_fin r
  change even22A331
    (-(33 * (46 * (0 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (0 + (r.val : ZMod 337)) + 25))) = true →
      (241639405291448151731969848530362550014613089667532079100936873602808979931184892674556039245298892798).testBit r.val = true := by decide

theorem even22_b25_s0_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (0 + (i : ZMod 337)) + 25))) = true) :
    (241639405291448151731969848530362550014613089667532079100936873602808979931184892674556039245298892798).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_337_fin r
  change even22A337
    (-(33 * (46 * (0 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (0 + (r.val : ZMod 347)) + 25))) = true →
      (286685139746978716658648582665633306646826716869210477419200700275932810845453442742758006422122195320831).testBit r.val = true := by decide

theorem even22_b25_s0_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (0 + (i : ZMod 347)) + 25))) = true) :
    (286685139746978716658648582665633306646826716869210477419200700275932810845453442742758006422122195320831).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_347_fin r
  change even22A347
    (-(33 * (46 * (0 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (0 + (r.val : ZMod 349)) + 25))) = true →
      (1146743771515587279634601556643694900207837687713015596446027372074441521604868366759915697257918056306687).testBit r.val = true := by decide

theorem even22_b25_s0_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (0 + (i : ZMod 349)) + 25))) = true) :
    (1146743771515587279634601556643694900207837687713015596446027372074441521604868366759915697257918056306687).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_349_fin r
  change even22A349
    (-(33 * (46 * (0 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 193518404153091962340478508591038074808937179439539720569680450257634351560862575820365889535) (.leaf 311 3910981759326128018703894861736621093517822681065773084350243907779465035062689970113954709501)) (.node (.leaf 313 16165917508190481493669212236072140220745806891590275650230411133261026952999586111980876857087) (.leaf 317 118310969933784382387167108800242568599454246706396644566256344288113932900734600431458045657086))) (.node (.node (.leaf 331 2592019158922691962767660400660528472567166557246903865028191220453678933189516797329685358430747597) (.leaf 337 241639405291448151731969848530362550014613089667532079100936873602808979931184892674556039245298892798)) (.node (.leaf 347 286685139746978716658648582665633306646826716869210477419200700275932810845453442742758006422122195320831) (.leaf 349 1146743771515587279634601556643694900207837687713015596446027372074441521604868366759915697257918056306687))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
