import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s3_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (48000000 + (r.val : ZMod 353)) + 17))) = true →
      (13756512206289069086850884462319969799477457377748275795533564101215685183588663644541140330050891491830647).testBit r.val = true := by decide

theorem even22_b17_s3_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (48000000 + (i : ZMod 353)) + 17))) = true) :
    (13756512206289069086850884462319969799477457377748275795533564101215685183588663644541140330050891491830647).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_353_fin r
  change even22A353
    (-(33 * (46 * (48000000 + ((i % 353 : ℕ) : ZMod 353)) + 17))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (48000000 + (r.val : ZMod 359)) + 17))) = true →
      (1100769447104127870635372602569048229103951084395727378303488008202854835929276919461533171018745778222923002).testBit r.val = true := by decide

theorem even22_b17_s3_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (48000000 + (i : ZMod 359)) + 17))) = true) :
    (1100769447104127870635372602569048229103951084395727378303488008202854835929276919461533171018745778222923002).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_359_fin r
  change even22A359
    (-(33 * (46 * (48000000 + ((i % 359 : ℕ) : ZMod 359)) + 17))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (48000000 + (r.val : ZMod 367)) + 17))) = true →
      (279476459841103895667991973958801138423868895515885693297126527994507820472494588434141876883755800117441724157).testBit r.val = true := by decide

theorem even22_b17_s3_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (48000000 + (i : ZMod 367)) + 17))) = true) :
    (279476459841103895667991973958801138423868895515885693297126527994507820472494588434141876883755800117441724157).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_367_fin r
  change even22A367
    (-(33 * (46 * (48000000 + ((i % 367 : ℕ) : ZMod 367)) + 17))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (48000000 + (r.val : ZMod 373)) + 17))) = true →
      (9525688715726293070868130240751877688496559317896358213974405529399038445428588552838954177871597053175473634207).testBit r.val = true := by decide

theorem even22_b17_s3_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (48000000 + (i : ZMod 373)) + 17))) = true) :
    (9525688715726293070868130240751877688496559317896358213974405529399038445428588552838954177871597053175473634207).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_373_fin r
  change even22A373
    (-(33 * (46 * (48000000 + ((i % 373 : ℕ) : ZMod 373)) + 17))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (48000000 + (r.val : ZMod 379)) + 17))) = true →
      (1207263617580755421751137717114919016153938137001171140178512187192825507686454056078581069212899125999099208269558).testBit r.val = true := by decide

theorem even22_b17_s3_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (48000000 + (i : ZMod 379)) + 17))) = true) :
    (1207263617580755421751137717114919016153938137001171140178512187192825507686454056078581069212899125999099208269558).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_379_fin r
  change even22A379
    (-(33 * (46 * (48000000 + ((i % 379 : ℕ) : ZMod 379)) + 17))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (48000000 + (r.val : ZMod 383)) + 17))) = true →
      (18315774996728297119358977221408254304691436398869764280318723368365237354032997828743635206229757517247030765285367).testBit r.val = true := by decide

theorem even22_b17_s3_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (48000000 + (i : ZMod 383)) + 17))) = true) :
    (18315774996728297119358977221408254304691436398869764280318723368365237354032997828743635206229757517247030765285367).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_383_fin r
  change even22A383
    (-(33 * (46 * (48000000 + ((i % 383 : ℕ) : ZMod 383)) + 17))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (48000000 + (r.val : ZMod 389)) + 17))) = true →
      (1260864198280609703295047585581898453889418992194267894859344124470557626558241024829538436518725208675819654347226619).testBit r.val = true := by decide

theorem even22_b17_s3_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (48000000 + (i : ZMod 389)) + 17))) = true) :
    (1260864198280609703295047585581898453889418992194267894859344124470557626558241024829538436518725208675819654347226619).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_389_fin r
  change even22A389
    (-(33 * (46 * (48000000 + ((i % 389 : ℕ) : ZMod 389)) + 17))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (48000000 + (r.val : ZMod 397)) + 17))) = true →
      (242085924266964539867658746897325685483577272045227001016218940547062447519148026947974468974638248095037306542286700543).testBit r.val = true := by decide

theorem even22_b17_s3_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (48000000 + (i : ZMod 397)) + 17))) = true) :
    (242085924266964539867658746897325685483577272045227001016218940547062447519148026947974468974638248095037306542286700543).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_397_fin r
  change even22A397
    (-(33 * (46 * (48000000 + ((i % 397 : ℕ) : ZMod 397)) + 17))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB17S3Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 13756512206289069086850884462319969799477457377748275795533564101215685183588663644541140330050891491830647) (.leaf 359 1100769447104127870635372602569048229103951084395727378303488008202854835929276919461533171018745778222923002)) (.node (.leaf 367 279476459841103895667991973958801138423868895515885693297126527994507820472494588434141876883755800117441724157) (.leaf 373 9525688715726293070868130240751877688496559317896358213974405529399038445428588552838954177871597053175473634207))) (.node (.node (.leaf 379 1207263617580755421751137717114919016153938137001171140178512187192825507686454056078581069212899125999099208269558) (.leaf 383 18315774996728297119358977221408254304691436398869764280318723368365237354032997828743635206229757517247030765285367)) (.node (.leaf 389 1260864198280609703295047585581898453889418992194267894859344124470557626558241024829538436518725208675819654347226619) (.leaf 397 242085924266964539867658746897325685483577272045227001016218940547062447519148026947974468974638248095037306542286700543))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S3Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S3Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
