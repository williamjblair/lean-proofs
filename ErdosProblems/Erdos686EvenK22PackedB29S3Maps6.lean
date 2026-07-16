import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s3_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (48000000 + (r.val : ZMod 401)) + 29))) = true →
      (5164498986598083074779377702466682779779310367182041409506477174447645647781527307627033993098499089981352771327602064895).testBit r.val = true := by decide

theorem even22_b29_s3_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (48000000 + (i : ZMod 401)) + 29))) = true) :
    (5164498986598083074779377702466682779779310367182041409506477174447645647781527307627033993098499089981352771327602064895).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_401_fin r
  change even22A401
    (-(33 * (46 * (48000000 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (48000000 + (r.val : ZMod 409)) + 29))) = true →
      (1239157160083421466866847840870868218509257465485296403161952185203662918609191422021687171825701264086522327044340618100607).testBit r.val = true := by decide

theorem even22_b29_s3_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (48000000 + (i : ZMod 409)) + 29))) = true) :
    (1239157160083421466866847840870868218509257465485296403161952185203662918609191422021687171825701264086522327044340618100607).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_409_fin r
  change even22A409
    (-(33 * (46 * (48000000 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (48000000 + (r.val : ZMod 419)) + 29))) = true →
      (1290381128750111777672928634914091379153554591824159457807289429513809527287637349371572945405061551469863955959376261414633037).testBit r.val = true := by decide

theorem even22_b29_s3_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (48000000 + (i : ZMod 419)) + 29))) = true) :
    (1290381128750111777672928634914091379153554591824159457807289429513809527287637349371572945405061551469863955959376261414633037).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_419_fin r
  change even22A419
    (-(33 * (46 * (48000000 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (48000000 + (r.val : ZMod 421)) + 29))) = true →
      (4526911230066564233774214216937534802068980095682282150100272990018596096112818695042271444453754091800765776566208776445599670).testBit r.val = true := by decide

theorem even22_b29_s3_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (48000000 + (i : ZMod 421)) + 29))) = true) :
    (4526911230066564233774214216937534802068980095682282150100272990018596096112818695042271444453754091800765776566208776445599670).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_421_fin r
  change even22A421
    (-(33 * (46 * (48000000 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (48000000 + (r.val : ZMod 431)) + 29))) = true →
      (4158798291708867885184534860435759239992695789733282593807036109580811770678950158226091828532470843601246679673330900708894965759).testBit r.val = true := by decide

theorem even22_b29_s3_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (48000000 + (i : ZMod 431)) + 29))) = true) :
    (4158798291708867885184534860435759239992695789733282593807036109580811770678950158226091828532470843601246679673330900708894965759).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_431_fin r
  change even22A431
    (-(33 * (46 * (48000000 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (48000000 + (r.val : ZMod 433)) + 29))) = true →
      (22094373164359135891396242626680541112929980876390363696625707331521449063507348423259740986166404950787021951672661385570747801599).testBit r.val = true := by decide

theorem even22_b29_s3_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (48000000 + (i : ZMod 433)) + 29))) = true) :
    (22094373164359135891396242626680541112929980876390363696625707331521449063507348423259740986166404950787021951672661385570747801599).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_433_fin r
  change even22A433
    (-(33 * (46 * (48000000 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (48000000 + (r.val : ZMod 439)) + 29))) = true →
      (1241029382623921646649219108254488797066954926800744779982554489081076422279162289696934554928111611601612411771165943727792106487807).testBit r.val = true := by decide

theorem even22_b29_s3_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (48000000 + (i : ZMod 439)) + 29))) = true) :
    (1241029382623921646649219108254488797066954926800744779982554489081076422279162289696934554928111611601612411771165943727792106487807).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_439_fin r
  change even22A439
    (-(33 * (46 * (48000000 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (48000000 + (r.val : ZMod 443)) + 29))) = true →
      (22536259272476274641414132020087706073161598477589684732486121711032007411913265986583572607841132911882977303895544367412966044167613).testBit r.val = true := by decide

theorem even22_b29_s3_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (48000000 + (i : ZMod 443)) + 29))) = true) :
    (22536259272476274641414132020087706073161598477589684732486121711032007411913265986583572607841132911882977303895544367412966044167613).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_443_fin r
  change even22A443
    (-(33 * (46 * (48000000 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S3Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5164498986598083074779377702466682779779310367182041409506477174447645647781527307627033993098499089981352771327602064895) (.leaf 409 1239157160083421466866847840870868218509257465485296403161952185203662918609191422021687171825701264086522327044340618100607)) (.node (.leaf 419 1290381128750111777672928634914091379153554591824159457807289429513809527287637349371572945405061551469863955959376261414633037) (.leaf 421 4526911230066564233774214216937534802068980095682282150100272990018596096112818695042271444453754091800765776566208776445599670))) (.node (.node (.leaf 431 4158798291708867885184534860435759239992695789733282593807036109580811770678950158226091828532470843601246679673330900708894965759) (.leaf 433 22094373164359135891396242626680541112929980876390363696625707331521449063507348423259740986166404950787021951672661385570747801599)) (.node (.leaf 439 1241029382623921646649219108254488797066954926800744779982554489081076422279162289696934554928111611601612411771165943727792106487807) (.leaf 443 22536259272476274641414132020087706073161598477589684732486121711032007411913265986583572607841132911882977303895544367412966044167613))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S3Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S3Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
