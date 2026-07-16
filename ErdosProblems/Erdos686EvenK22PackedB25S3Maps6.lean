import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (48000000 + (r.val : ZMod 401)) + 25))) = true →
      (5154087409886794383114928168131837134999121891584616399458940779887600523648749235518286668698893507203561436072741173183).testBit r.val = true := by decide

theorem even22_b25_s3_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (48000000 + (i : ZMod 401)) + 25))) = true) :
    (5154087409886794383114928168131837134999121891584616399458940779887600523648749235518286668698893507203561436072741173183).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_401_fin r
  change even22A401
    (-(33 * (46 * (48000000 + ((i % 401 : ℕ) : ZMod 401)) + 25))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (48000000 + (r.val : ZMod 409)) + 25))) = true →
      (1322111937541910569876305892235135946963800629675016770819412774931057672239462439139230793829846146457252583843615628787711).testBit r.val = true := by decide

theorem even22_b25_s3_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (48000000 + (i : ZMod 409)) + 25))) = true) :
    (1322111937541910569876305892235135946963800629675016770819412774931057672239462439139230793829846146457252583843615628787711).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_409_fin r
  change even22A409
    (-(33 * (46 * (48000000 + ((i % 409 : ℕ) : ZMod 409)) + 25))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (48000000 + (r.val : ZMod 419)) + 25))) = true →
      (1353832294767686299158357914089007947746854644562541000218343070719057857531809469217949380382053071460426383152118904580470398).testBit r.val = true := by decide

theorem even22_b25_s3_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (48000000 + (i : ZMod 419)) + 25))) = true) :
    (1353832294767686299158357914089007947746854644562541000218343070719057857531809469217949380382053071460426383152118904580470398).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_419_fin r
  change even22A419
    (-(33 * (46 * (48000000 + ((i % 419 : ℕ) : ZMod 419)) + 25))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (48000000 + (r.val : ZMod 421)) + 25))) = true →
      (5243474156612244794749836912786416978329969166869813714411341649167189689973652674879514333385459079292432131843796523204214735).testBit r.val = true := by decide

theorem even22_b25_s3_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (48000000 + (i : ZMod 421)) + 25))) = true) :
    (5243474156612244794749836912786416978329969166869813714411341649167189689973652674879514333385459079292432131843796523204214735).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_421_fin r
  change even22A421
    (-(33 * (46 * (48000000 + ((i % 421 : ℕ) : ZMod 421)) + 25))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (48000000 + (r.val : ZMod 431)) + 25))) = true →
      (5496577245430469707203359397193917133149067541012505302826949609430993008138860225591185021683834400389597961334688936749848002367).testBit r.val = true := by decide

theorem even22_b25_s3_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (48000000 + (i : ZMod 431)) + 25))) = true) :
    (5496577245430469707203359397193917133149067541012505302826949609430993008138860225591185021683834400389597961334688936749848002367).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_431_fin r
  change even22A431
    (-(33 * (46 * (48000000 + ((i % 431 : ℕ) : ZMod 431)) + 25))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (48000000 + (r.val : ZMod 433)) + 25))) = true →
      (22007388775427669553233695892610310008773134044936816710086360558239542831642437900301361999543568104774851741169903598221276217343).testBit r.val = true := by decide

theorem even22_b25_s3_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (48000000 + (i : ZMod 433)) + 25))) = true) :
    (22007388775427669553233695892610310008773134044936816710086360558239542831642437900301361999543568104774851741169903598221276217343).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_433_fin r
  change even22A433
    (-(33 * (46 * (48000000 + ((i % 433 : ℕ) : ZMod 433)) + 25))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (48000000 + (r.val : ZMod 439)) + 25))) = true →
      (1375243827674372233370528721801655714623934053995063255550254388534809074781042905085663266707825584084365915644698729395639946313711).testBit r.val = true := by decide

theorem even22_b25_s3_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (48000000 + (i : ZMod 439)) + 25))) = true) :
    (1375243827674372233370528721801655714623934053995063255550254388534809074781042905085663266707825584084365915644698729395639946313711).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_439_fin r
  change even22A439
    (-(33 * (46 * (48000000 + ((i % 439 : ℕ) : ZMod 439)) + 25))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (48000000 + (r.val : ZMod 443)) + 25))) = true →
      (22483571769742539309148541151067800390452169917644730831376319001687603316126444945365689644755024146130628258625111163529346575499199).testBit r.val = true := by decide

theorem even22_b25_s3_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (48000000 + (i : ZMod 443)) + 25))) = true) :
    (22483571769742539309148541151067800390452169917644730831376319001687603316126444945365689644755024146130628258625111163529346575499199).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_443_fin r
  change even22A443
    (-(33 * (46 * (48000000 + ((i % 443 : ℕ) : ZMod 443)) + 25))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5154087409886794383114928168131837134999121891584616399458940779887600523648749235518286668698893507203561436072741173183) (.leaf 409 1322111937541910569876305892235135946963800629675016770819412774931057672239462439139230793829846146457252583843615628787711)) (.node (.leaf 419 1353832294767686299158357914089007947746854644562541000218343070719057857531809469217949380382053071460426383152118904580470398) (.leaf 421 5243474156612244794749836912786416978329969166869813714411341649167189689973652674879514333385459079292432131843796523204214735))) (.node (.node (.leaf 431 5496577245430469707203359397193917133149067541012505302826949609430993008138860225591185021683834400389597961334688936749848002367) (.leaf 433 22007388775427669553233695892610310008773134044936816710086360558239542831642437900301361999543568104774851741169903598221276217343)) (.node (.leaf 439 1375243827674372233370528721801655714623934053995063255550254388534809074781042905085663266707825584084365915644698729395639946313711) (.leaf 443 22483571769742539309148541151067800390452169917644730831376319001687603316126444945365689644755024146130628258625111163529346575499199))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
