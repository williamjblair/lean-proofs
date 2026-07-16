import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s4_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (64000000 + (r.val : ZMod 353)) + 17))) = true →
      (15911128056665809414937339619989036584220069907089411149581493220766067097725533753520595433135968746192893).testBit r.val = true := by decide

theorem even22_b17_s4_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (64000000 + (i : ZMod 353)) + 17))) = true) :
    (15911128056665809414937339619989036584220069907089411149581493220766067097725533753520595433135968746192893).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_353_fin r
  change even22A353
    (-(33 * (46 * (64000000 + ((i % 353 : ℕ) : ZMod 353)) + 17))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (64000000 + (r.val : ZMod 359)) + 17))) = true →
      (1095118707717030304728811424042330339885660366445182437213087796103607495846778696538231292833924776980346687).testBit r.val = true := by decide

theorem even22_b17_s4_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (64000000 + (i : ZMod 359)) + 17))) = true) :
    (1095118707717030304728811424042330339885660366445182437213087796103607495846778696538231292833924776980346687).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_359_fin r
  change even22A359
    (-(33 * (46 * (64000000 + ((i % 359 : ℕ) : ZMod 359)) + 17))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (64000000 + (r.val : ZMod 367)) + 17))) = true →
      (225125160717064095927637295766340356906007924752907342080621011278961028969979798121050018540676257768963571583).testBit r.val = true := by decide

theorem even22_b17_s4_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (64000000 + (i : ZMod 367)) + 17))) = true) :
    (225125160717064095927637295766340356906007924752907342080621011278961028969979798121050018540676257768963571583).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_367_fin r
  change even22A367
    (-(33 * (46 * (64000000 + ((i % 367 : ℕ) : ZMod 367)) + 17))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (64000000 + (r.val : ZMod 373)) + 17))) = true →
      (19239260837103353478163741741864974437983575849624869870819884798390911004628259862442587729001401420058623736574).testBit r.val = true := by decide

theorem even22_b17_s4_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (64000000 + (i : ZMod 373)) + 17))) = true) :
    (19239260837103353478163741741864974437983575849624869870819884798390911004628259862442587729001401420058623736574).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_373_fin r
  change even22A373
    (-(33 * (46 * (64000000 + ((i % 373 : ℕ) : ZMod 373)) + 17))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (64000000 + (r.val : ZMod 379)) + 17))) = true →
      (1192834022292177825582936510326972259059468757076226672312272814517387566666202222930382080337698701980185980302838).testBit r.val = true := by decide

theorem even22_b17_s4_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (64000000 + (i : ZMod 379)) + 17))) = true) :
    (1192834022292177825582936510326972259059468757076226672312272814517387566666202222930382080337698701980185980302838).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_379_fin r
  change even22A379
    (-(33 * (46 * (64000000 + ((i % 379 : ℕ) : ZMod 379)) + 17))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (64000000 + (r.val : ZMod 383)) + 17))) = true →
      (19695892064053415696891313359617354303618787470181124579725248864123663821500734695807789615241286627977106275956735).testBit r.val = true := by decide

theorem even22_b17_s4_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (64000000 + (i : ZMod 383)) + 17))) = true) :
    (19695892064053415696891313359617354303618787470181124579725248864123663821500734695807789615241286627977106275956735).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_383_fin r
  change even22A383
    (-(33 * (46 * (64000000 + ((i % 383 : ℕ) : ZMod 383)) + 17))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (64000000 + (r.val : ZMod 389)) + 17))) = true →
      (1241162894277114178673415543114920454157986054874998758079452941610291124338801102115911530513196282749976174521221119).testBit r.val = true := by decide

theorem even22_b17_s4_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (64000000 + (i : ZMod 389)) + 17))) = true) :
    (1241162894277114178673415543114920454157986054874998758079452941610291124338801102115911530513196282749976174521221119).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_389_fin r
  change even22A389
    (-(33 * (46 * (64000000 + ((i % 389 : ℕ) : ZMod 389)) + 17))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (64000000 + (r.val : ZMod 397)) + 17))) = true →
      (282433537122716495768341105926512731038508345738422044767141309310151805797516778511231340328227580343797217520053600127).testBit r.val = true := by decide

theorem even22_b17_s4_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (64000000 + (i : ZMod 397)) + 17))) = true) :
    (282433537122716495768341105926512731038508345738422044767141309310151805797516778511231340328227580343797217520053600127).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_397_fin r
  change even22A397
    (-(33 * (46 * (64000000 + ((i % 397 : ℕ) : ZMod 397)) + 17))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB17S4Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 15911128056665809414937339619989036584220069907089411149581493220766067097725533753520595433135968746192893) (.leaf 359 1095118707717030304728811424042330339885660366445182437213087796103607495846778696538231292833924776980346687)) (.node (.leaf 367 225125160717064095927637295766340356906007924752907342080621011278961028969979798121050018540676257768963571583) (.leaf 373 19239260837103353478163741741864974437983575849624869870819884798390911004628259862442587729001401420058623736574))) (.node (.node (.leaf 379 1192834022292177825582936510326972259059468757076226672312272814517387566666202222930382080337698701980185980302838) (.leaf 383 19695892064053415696891313359617354303618787470181124579725248864123663821500734695807789615241286627977106275956735)) (.node (.leaf 389 1241162894277114178673415543114920454157986054874998758079452941610291124338801102115911530513196282749976174521221119) (.leaf 397 282433537122716495768341105926512731038508345738422044767141309310151805797516778511231340328227580343797217520053600127))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S4Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S4Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
