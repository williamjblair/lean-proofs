import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (48000000 + (r.val : ZMod 353)) + 25))) = true →
      (18166531309757668507256929778254773798328664652785388033437753140791354999671780716133490926258814702808047).testBit r.val = true := by decide

theorem even22_b25_s3_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (48000000 + (i : ZMod 353)) + 25))) = true) :
    (18166531309757668507256929778254773798328664652785388033437753140791354999671780716133490926258814702808047).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_353_fin r
  change even22A353
    (-(33 * (46 * (48000000 + ((i % 353 : ℕ) : ZMod 353)) + 25))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (48000000 + (r.val : ZMod 359)) + 25))) = true →
      (1126097172908146666632291952674325241771798745664726325910152152236515373311950895848241273839491067102093111).testBit r.val = true := by decide

theorem even22_b25_s3_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (48000000 + (i : ZMod 359)) + 25))) = true) :
    (1126097172908146666632291952674325241771798745664726325910152152236515373311950895848241273839491067102093111).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_359_fin r
  change even22A359
    (-(33 * (46 * (48000000 + ((i % 359 : ℕ) : ZMod 359)) + 25))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (48000000 + (r.val : ZMod 367)) + 25))) = true →
      (299436884542931450519789880244868916321084971868375568802252885459700465465241399394780956294550158145110339510).testBit r.val = true := by decide

theorem even22_b25_s3_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (48000000 + (i : ZMod 367)) + 25))) = true) :
    (299436884542931450519789880244868916321084971868375568802252885459700465465241399394780956294550158145110339510).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_367_fin r
  change even22A367
    (-(33 * (46 * (48000000 + ((i % 367 : ℕ) : ZMod 367)) + 25))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (48000000 + (r.val : ZMod 373)) + 25))) = true →
      (8942626323228974110046090259849506781276772401155373121755970639154250399361406863596681919412304832886332186623).testBit r.val = true := by decide

theorem even22_b25_s3_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (48000000 + (i : ZMod 373)) + 25))) = true) :
    (8942626323228974110046090259849506781276772401155373121755970639154250399361406863596681919412304832886332186623).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_373_fin r
  change even22A373
    (-(33 * (46 * (48000000 + ((i % 373 : ℕ) : ZMod 373)) + 25))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (48000000 + (r.val : ZMod 379)) + 25))) = true →
      (615653952114933078571184118289237173820372330188948631395602499038018986269918092785675978425875025054868814389103).testBit r.val = true := by decide

theorem even22_b25_s3_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (48000000 + (i : ZMod 379)) + 25))) = true) :
    (615653952114933078571184118289237173820372330188948631395602499038018986269918092785675978425875025054868814389103).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_379_fin r
  change even22A379
    (-(33 * (46 * (48000000 + ((i % 379 : ℕ) : ZMod 379)) + 25))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (48000000 + (r.val : ZMod 383)) + 25))) = true →
      (19699800644242538716238082201704436609548797678654971647729339062364757228434689892341271410337888315105552482955263).testBit r.val = true := by decide

theorem even22_b25_s3_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (48000000 + (i : ZMod 383)) + 25))) = true) :
    (19699800644242538716238082201704436609548797678654971647729339062364757228434689892341271410337888315105552482955263).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_383_fin r
  change even22A383
    (-(33 * (46 * (48000000 + ((i % 383 : ℕ) : ZMod 383)) + 25))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (48000000 + (r.val : ZMod 389)) + 25))) = true →
      (1260825681892698021081029118135362911903257942138054362376802909134376829377698625179610886149461628770438377489039357).testBit r.val = true := by decide

theorem even22_b25_s3_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (48000000 + (i : ZMod 389)) + 25))) = true) :
    (1260825681892698021081029118135362911903257942138054362376802909134376829377698625179610886149461628770438377489039357).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_389_fin r
  change even22A389
    (-(33 * (46 * (48000000 + ((i % 389 : ℕ) : ZMod 389)) + 25))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (48000000 + (r.val : ZMod 397)) + 25))) = true →
      (160128521868132327487270785788560371853171065251178495702440280803843339196510825168353939316906991083653856041554149374).testBit r.val = true := by decide

theorem even22_b25_s3_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (48000000 + (i : ZMod 397)) + 25))) = true) :
    (160128521868132327487270785788560371853171065251178495702440280803843339196510825168353939316906991083653856041554149374).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_397_fin r
  change even22A397
    (-(33 * (46 * (48000000 + ((i % 397 : ℕ) : ZMod 397)) + 25))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18166531309757668507256929778254773798328664652785388033437753140791354999671780716133490926258814702808047) (.leaf 359 1126097172908146666632291952674325241771798745664726325910152152236515373311950895848241273839491067102093111)) (.node (.leaf 367 299436884542931450519789880244868916321084971868375568802252885459700465465241399394780956294550158145110339510) (.leaf 373 8942626323228974110046090259849506781276772401155373121755970639154250399361406863596681919412304832886332186623))) (.node (.node (.leaf 379 615653952114933078571184118289237173820372330188948631395602499038018986269918092785675978425875025054868814389103) (.leaf 383 19699800644242538716238082201704436609548797678654971647729339062364757228434689892341271410337888315105552482955263)) (.node (.leaf 389 1260825681892698021081029118135362911903257942138054362376802909134376829377698625179610886149461628770438377489039357) (.leaf 397 160128521868132327487270785788560371853171065251178495702440280803843339196510825168353939316906991083653856041554149374))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
