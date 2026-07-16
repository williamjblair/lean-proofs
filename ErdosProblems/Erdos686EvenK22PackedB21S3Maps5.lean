import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (48000000 + (r.val : ZMod 353)) + 21))) = true →
      (18043381445053730693912657446382052687234948842752875223787799671136924422315671675406904215266906572027775).testBit r.val = true := by decide

theorem even22_b21_s3_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (48000000 + (i : ZMod 353)) + 21))) = true) :
    (18043381445053730693912657446382052687234948842752875223787799671136924422315671675406904215266906572027775).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_353_fin r
  change even22A353
    (-(33 * (46 * (48000000 + ((i % 353 : ℕ) : ZMod 353)) + 21))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (48000000 + (r.val : ZMod 359)) + 21))) = true →
      (586203841888680803410407988655359874017934863778694776390287226707717633920338134446639879785117346476915711).testBit r.val = true := by decide

theorem even22_b21_s3_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (48000000 + (i : ZMod 359)) + 21))) = true) :
    (586203841888680803410407988655359874017934863778694776390287226707717633920338134446639879785117346476915711).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_359_fin r
  change even22A359
    (-(33 * (46 * (48000000 + ((i % 359 : ℕ) : ZMod 359)) + 21))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (48000000 + (r.val : ZMod 367)) + 21))) = true →
      (290907346389317347562022760103336820136238480715942650089949770704295504170677337879534311049616280338233786349).testBit r.val = true := by decide

theorem even22_b21_s3_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (48000000 + (i : ZMod 367)) + 21))) = true) :
    (290907346389317347562022760103336820136238480715942650089949770704295504170677337879534311049616280338233786349).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_367_fin r
  change even22A367
    (-(33 * (46 * (48000000 + ((i % 367 : ℕ) : ZMod 367)) + 21))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (48000000 + (r.val : ZMod 373)) + 21))) = true →
      (19239259402353270152101681037779529818620381983608899761643047812141204856645072800867690918944522585304297635583).testBit r.val = true := by decide

theorem even22_b21_s3_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (48000000 + (i : ZMod 373)) + 21))) = true) :
    (19239259402353270152101681037779529818620381983608899761643047812141204856645072800867690918944522585304297635583).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_373_fin r
  change even22A373
    (-(33 * (46 * (48000000 + ((i % 373 : ℕ) : ZMod 373)) + 21))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (48000000 + (r.val : ZMod 379)) + 21))) = true →
      (1231011483517613231769932968943852419880927044982215531821305413341430145734311976410348766161600556540268731957247).testBit r.val = true := by decide

theorem even22_b21_s3_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (48000000 + (i : ZMod 379)) + 21))) = true) :
    (1231011483517613231769932968943852419880927044982215531821305413341430145734311976410348766161600556540268731957247).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_379_fin r
  change even22A379
    (-(33 * (46 * (48000000 + ((i % 379 : ℕ) : ZMod 379)) + 21))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (48000000 + (r.val : ZMod 383)) + 21))) = true →
      (19700852642251048317016914596140709214666464162066141441095157704176206666841896295537967959728338876412434172313455).testBit r.val = true := by decide

theorem even22_b21_s3_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (48000000 + (i : ZMod 383)) + 21))) = true) :
    (19700852642251048317016914596140709214666464162066141441095157704176206666841896295537967959728338876412434172313455).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_383_fin r
  change even22A383
    (-(33 * (46 * (48000000 + ((i % 383 : ℕ) : ZMod 383)) + 21))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (48000000 + (r.val : ZMod 389)) + 21))) = true →
      (1255900468988397827786210461550610091467009132031035756983814404271286599317296942481742054194980803625068465976246267).testBit r.val = true := by decide

theorem even22_b21_s3_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (48000000 + (i : ZMod 389)) + 21))) = true) :
    (1255900468988397827786210461550610091467009132031035756983814404271286599317296942481742054194980803625068465976246267).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_389_fin r
  change even22A389
    (-(33 * (46 * (48000000 + ((i % 389 : ℕ) : ZMod 389)) + 21))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (48000000 + (r.val : ZMod 397)) + 21))) = true →
      (322647464179669245279879101398787240133503181276987916822795728248526863842768234386047693399020252832142801786698723198).testBit r.val = true := by decide

theorem even22_b21_s3_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (48000000 + (i : ZMod 397)) + 21))) = true) :
    (322647464179669245279879101398787240133503181276987916822795728248526863842768234386047693399020252832142801786698723198).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_397_fin r
  change even22A397
    (-(33 * (46 * (48000000 + ((i % 397 : ℕ) : ZMod 397)) + 21))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18043381445053730693912657446382052687234948842752875223787799671136924422315671675406904215266906572027775) (.leaf 359 586203841888680803410407988655359874017934863778694776390287226707717633920338134446639879785117346476915711)) (.node (.leaf 367 290907346389317347562022760103336820136238480715942650089949770704295504170677337879534311049616280338233786349) (.leaf 373 19239259402353270152101681037779529818620381983608899761643047812141204856645072800867690918944522585304297635583))) (.node (.node (.leaf 379 1231011483517613231769932968943852419880927044982215531821305413341430145734311976410348766161600556540268731957247) (.leaf 383 19700852642251048317016914596140709214666464162066141441095157704176206666841896295537967959728338876412434172313455)) (.node (.leaf 389 1255900468988397827786210461550610091467009132031035756983814404271286599317296942481742054194980803625068465976246267) (.leaf 397 322647464179669245279879101398787240133503181276987916822795728248526863842768234386047693399020252832142801786698723198))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
