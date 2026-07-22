import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s3_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (48000000 + (r.val : ZMod 353)) + 29))) = true →
      (18345608639231908577241663741753332021899727779971637503897316543832963165168834131609287938649223665286847).testBit r.val = true := by decide

theorem even22_b29_s3_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (48000000 + (i : ZMod 353)) + 29))) = true) :
    (18345608639231908577241663741753332021899727779971637503897316543832963165168834131609287938649223665286847).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_353_fin r
  change even22A353
    (-(33 * (46 * (48000000 + ((i % 353 : ℕ) : ZMod 353)) + 29))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (48000000 + (r.val : ZMod 359)) + 29))) = true →
      (733776141812314140988119067251401811961185562516139156690794507222782897375952678419582271785659223620189182).testBit r.val = true := by decide

theorem even22_b29_s3_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (48000000 + (i : ZMod 359)) + 29))) = true) :
    (733776141812314140988119067251401811961185562516139156690794507222782897375952678419582271785659223620189182).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_359_fin r
  change even22A359
    (-(33 * (46 * (48000000 + ((i % 359 : ℕ) : ZMod 359)) + 29))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (48000000 + (r.val : ZMod 367)) + 29))) = true →
      (300535179845088358255187735518273258212918160228892338155352859258421613555674928081329975181190756236997423103).testBit r.val = true := by decide

theorem even22_b29_s3_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (48000000 + (i : ZMod 367)) + 29))) = true) :
    (300535179845088358255187735518273258212918160228892338155352859258421613555674928081329975181190756236997423103).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_367_fin r
  change even22A367
    (-(33 * (46 * (48000000 + ((i % 367 : ℕ) : ZMod 367)) + 29))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (48000000 + (r.val : ZMod 373)) + 29))) = true →
      (4809815209380142887371324341515322566435803304082316811874593549471412814931518087369398240502817216323416752126).testBit r.val = true := by decide

theorem even22_b29_s3_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (48000000 + (i : ZMod 373)) + 29))) = true) :
    (4809815209380142887371324341515322566435803304082316811874593549471412814931518087369398240502817216323416752126).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_373_fin r
  change even22A373
    (-(33 * (46 * (48000000 + ((i % 373 : ℕ) : ZMod 373)) + 29))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (48000000 + (r.val : ZMod 379)) + 29))) = true →
      (1221392156199867271172780708987971568530266252768647691112407869320590894979917850215183131145655219820208423172095).testBit r.val = true := by decide

theorem even22_b29_s3_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (48000000 + (i : ZMod 379)) + 29))) = true) :
    (1221392156199867271172780708987971568530266252768647691112407869320590894979917850215183131145655219820208423172095).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_379_fin r
  change even22A379
    (-(33 * (46 * (48000000 + ((i % 379 : ℕ) : ZMod 379)) + 29))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (48000000 + (r.val : ZMod 383)) + 29))) = true →
      (19354523748535785153478674091486388436378820421839344565340718586879227160501629174162444255770161812855362974351359).testBit r.val = true := by decide

theorem even22_b29_s3_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (48000000 + (i : ZMod 383)) + 29))) = true) :
    (19354523748535785153478674091486388436378820421839344565340718586879227160501629174162444255770161812855362974351359).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_383_fin r
  change even22A383
    (-(33 * (46 * (48000000 + ((i % 383 : ℕ) : ZMod 383)) + 29))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (48000000 + (r.val : ZMod 389)) + 29))) = true →
      (1260844958729928501632656320567789318337156573059406114140658970530271717808663562184934894189868940136909912173051903).testBit r.val = true := by decide

theorem even22_b29_s3_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (48000000 + (i : ZMod 389)) + 29))) = true) :
    (1260844958729928501632656320567789318337156573059406114140658970530271717808663562184934894189868940136909912173051903).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_389_fin r
  change even22A389
    (-(33 * (46 * (48000000 + ((i % 389 : ℕ) : ZMod 389)) + 29))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (48000000 + (r.val : ZMod 397)) + 29))) = true →
      (322544822404283415539477649762712424306632450598604473810634632658722839577693665156202006610798857281153805977808502783).testBit r.val = true := by decide

theorem even22_b29_s3_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (48000000 + (i : ZMod 397)) + 29))) = true) :
    (322544822404283415539477649762712424306632450598604473810634632658722839577693665156202006610798857281153805977808502783).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_397_fin r
  change even22A397
    (-(33 * (46 * (48000000 + ((i % 397 : ℕ) : ZMod 397)) + 29))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB29S3Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18345608639231908577241663741753332021899727779971637503897316543832963165168834131609287938649223665286847) (.leaf 359 733776141812314140988119067251401811961185562516139156690794507222782897375952678419582271785659223620189182)) (.node (.leaf 367 300535179845088358255187735518273258212918160228892338155352859258421613555674928081329975181190756236997423103) (.leaf 373 4809815209380142887371324341515322566435803304082316811874593549471412814931518087369398240502817216323416752126))) (.node (.node (.leaf 379 1221392156199867271172780708987971568530266252768647691112407869320590894979917850215183131145655219820208423172095) (.leaf 383 19354523748535785153478674091486388436378820421839344565340718586879227160501629174162444255770161812855362974351359)) (.node (.leaf 389 1260844958729928501632656320567789318337156573059406114140658970530271717808663562184934894189868940136909912173051903) (.leaf 397 322544822404283415539477649762712424306632450598604473810634632658722839577693665156202006610798857281153805977808502783))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S3Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S3Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
