import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (48000000 + (r.val : ZMod 449)) + 25))) = true →
      (726838724210981396120646434233694882739527885215979678830988903303140659594323497074034089359911761505873320274236837231340603949678589).testBit r.val = true := by decide

theorem even22_b25_s3_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (48000000 + (i : ZMod 449)) + 25))) = true) :
    (726838724210981396120646434233694882739527885215979678830988903303140659594323497074034089359911761505873320274236837231340603949678589).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_449_fin r
  change even22A449
    (-(33 * (46 * (48000000 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (48000000 + (r.val : ZMod 457)) + 25))) = true →
      (372118712869278024627424679082077465070389857201160016741711181307078576312618236738933015596563707610884301562802168870397612670832082932).testBit r.val = true := by decide

theorem even22_b25_s3_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (48000000 + (i : ZMod 457)) + 25))) = true) :
    (372118712869278024627424679082077465070389857201160016741711181307078576312618236738933015596563707610884301562802168870397612670832082932).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_457_fin r
  change even22A457
    (-(33 * (46 * (48000000 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (48000000 + (r.val : ZMod 461)) + 25))) = true →
      (5582121225133893899436371063559349860990170470821478884603283541965291327887192701734349162585198569233564760530689767824033014462582357999).testBit r.val = true := by decide

theorem even22_b25_s3_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (48000000 + (i : ZMod 461)) + 25))) = true) :
    (5582121225133893899436371063559349860990170470821478884603283541965291327887192701734349162585198569233564760530689767824033014462582357999).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_461_fin r
  change even22A461
    (-(33 * (46 * (48000000 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (48000000 + (r.val : ZMod 463)) + 25))) = true →
      (17815543527582469104032275532285136597561023346726701925648966014238953772811418099491355641484048598768489808709210039854793287134151687676).testBit r.val = true := by decide

theorem even22_b25_s3_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (48000000 + (i : ZMod 463)) + 25))) = true) :
    (17815543527582469104032275532285136597561023346726701925648966014238953772811418099491355641484048598768489808709210039854793287134151687676).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_463_fin r
  change even22A463
    (-(33 * (46 * (48000000 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (48000000 + (r.val : ZMod 467)) + 25))) = true →
      (374118379724613387012947612904966465865911920047497686381198798652922292644957562244349904060295438036838821583574823851507609270754131832219).testBit r.val = true := by decide

theorem even22_b25_s3_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (48000000 + (i : ZMod 467)) + 25))) = true) :
    (374118379724613387012947612904966465865911920047497686381198798652922292644957562244349904060295438036838821583574823851507609270754131832219).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_467_fin r
  change even22A467
    (-(33 * (46 * (48000000 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (48000000 + (r.val : ZMod 479)) + 25))) = true →
      (1560874271611367183070426624481426542505291475650803484772174396728700230944299746979547713041708528891245418207410632048285998425678456687123398).testBit r.val = true := by decide

theorem even22_b25_s3_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (48000000 + (i : ZMod 479)) + 25))) = true) :
    (1560874271611367183070426624481426542505291475650803484772174396728700230944299746979547713041708528891245418207410632048285998425678456687123398).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_479_fin r
  change even22A479
    (-(33 * (46 * (48000000 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (48000000 + (r.val : ZMod 487)) + 25))) = true →
      (397827830880706694248390219064338504615715877984740616387029111611755203323837292568840195489514889388494871549927023503976831998816973011511344590).testBit r.val = true := by decide

theorem even22_b25_s3_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (48000000 + (i : ZMod 487)) + 25))) = true) :
    (397827830880706694248390219064338504615715877984740616387029111611755203323837292568840195489514889388494871549927023503976831998816973011511344590).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_487_fin r
  change even22A487
    (-(33 * (46 * (48000000 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (48000000 + (r.val : ZMod 491)) + 25))) = true →
      (5992488973503785245267138469990055851444509014046566675797169192409407140334117268671399775424362288050896246613077619563627067653075736861507059579).testBit r.val = true := by decide

theorem even22_b25_s3_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (48000000 + (i : ZMod 491)) + 25))) = true) :
    (5992488973503785245267138469990055851444509014046566675797169192409407140334117268671399775424362288050896246613077619563627067653075736861507059579).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_491_fin r
  change even22A491
    (-(33 * (46 * (48000000 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 726838724210981396120646434233694882739527885215979678830988903303140659594323497074034089359911761505873320274236837231340603949678589) (.leaf 457 372118712869278024627424679082077465070389857201160016741711181307078576312618236738933015596563707610884301562802168870397612670832082932)) (.node (.leaf 461 5582121225133893899436371063559349860990170470821478884603283541965291327887192701734349162585198569233564760530689767824033014462582357999) (.leaf 463 17815543527582469104032275532285136597561023346726701925648966014238953772811418099491355641484048598768489808709210039854793287134151687676))) (.node (.node (.leaf 467 374118379724613387012947612904966465865911920047497686381198798652922292644957562244349904060295438036838821583574823851507609270754131832219) (.leaf 479 1560874271611367183070426624481426542505291475650803484772174396728700230944299746979547713041708528891245418207410632048285998425678456687123398)) (.node (.leaf 487 397827830880706694248390219064338504615715877984740616387029111611755203323837292568840195489514889388494871549927023503976831998816973011511344590) (.leaf 491 5992488973503785245267138469990055851444509014046566675797169192409407140334117268671399775424362288050896246613077619563627067653075736861507059579))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
