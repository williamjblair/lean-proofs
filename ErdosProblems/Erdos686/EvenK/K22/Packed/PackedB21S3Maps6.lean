import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (48000000 + (r.val : ZMod 401)) + 21))) = true →
      (3873059591458812766741426108902430766822501499432625347777210124788499666793561585738608660509619508166012143938769518591).testBit r.val = true := by decide

theorem even22_b21_s3_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (48000000 + (i : ZMod 401)) + 21))) = true) :
    (3873059591458812766741426108902430766822501499432625347777210124788499666793561585738608660509619508166012143938769518591).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_401_fin r
  change even22A401
    (-(33 * (46 * (48000000 + ((i % 401 : ℕ) : ZMod 401)) + 21))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (48000000 + (r.val : ZMod 409)) + 21))) = true →
      (1311742570712801348227258946323951767256853705785639522093206391152415180536305004388446401942349970285085625979572401717247).testBit r.val = true := by decide

theorem even22_b21_s3_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (48000000 + (i : ZMod 409)) + 21))) = true) :
    (1311742570712801348227258946323951767256853705785639522093206391152415180536305004388446401942349970285085625979572401717247).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_409_fin r
  change even22A409
    (-(33 * (46 * (48000000 + ((i % 409 : ℕ) : ZMod 409)) + 21))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (48000000 + (r.val : ZMod 419)) + 21))) = true →
      (1345827315416774877567828982974844659497902965606548691410909857571498065234147430191692231973172691737102112716252352884979711).testBit r.val = true := by decide

theorem even22_b21_s3_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (48000000 + (i : ZMod 419)) + 21))) = true) :
    (1345827315416774877567828982974844659497902965606548691410909857571498065234147430191692231973172691737102112716252352884979711).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_419_fin r
  change even22A419
    (-(33 * (46 * (48000000 + ((i % 419 : ℕ) : ZMod 419)) + 21))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (48000000 + (r.val : ZMod 421)) + 21))) = true →
      (5394216705013212217263000087350837417668891724487993692377083290793698991312426433622871120155042251563137661539354768294935539).testBit r.val = true := by decide

theorem even22_b21_s3_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (48000000 + (i : ZMod 421)) + 21))) = true) :
    (5394216705013212217263000087350837417668891724487993692377083290793698991312426433622871120155042251563137661539354768294935539).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_421_fin r
  change even22A421
    (-(33 * (46 * (48000000 + ((i % 421 : ℕ) : ZMod 421)) + 21))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (48000000 + (r.val : ZMod 431)) + 21))) = true →
      (4687679424506659743238142993089425043353464239539951717486009664860729913650797906174079412428728227940017490306010477398690987991).testBit r.val = true := by decide

theorem even22_b21_s3_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (48000000 + (i : ZMod 431)) + 21))) = true) :
    (4687679424506659743238142993089425043353464239539951717486009664860729913650797906174079412428728227940017490306010477398690987991).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_431_fin r
  change even22A431
    (-(33 * (46 * (48000000 + ((i % 431 : ℕ) : ZMod 431)) + 21))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (48000000 + (r.val : ZMod 433)) + 21))) = true →
      (22181352264518768394711863273574781322051236246474833661070517083085035023292167692089561844790763196489065878302759580196088575991).testBit r.val = true := by decide

theorem even22_b21_s3_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (48000000 + (i : ZMod 433)) + 21))) = true) :
    (22181352264518768394711863273574781322051236246474833661070517083085035023292167692089561844790763196489065878302759580196088575991).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_433_fin r
  change even22A433
    (-(33 * (46 * (48000000 + ((i % 433 : ℕ) : ZMod 433)) + 21))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (48000000 + (r.val : ZMod 439)) + 21))) = true →
      (1419563475810072904056936606004676176897599537905814395301878414842783920618688801505092204393253075654825490565551763240775353081851).testBit r.val = true := by decide

theorem even22_b21_s3_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (48000000 + (i : ZMod 439)) + 21))) = true) :
    (1419563475810072904056936606004676176897599537905814395301878414842783920618688801505092204393253075654825490565551763240775353081851).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_439_fin r
  change even22A439
    (-(33 * (46 * (48000000 + ((i % 439 : ℕ) : ZMod 439)) + 21))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (48000000 + (r.val : ZMod 443)) + 21))) = true →
      (9897737545394987958529492030541029962965146887423642170050110439507306289576801415006824567926880521678256213173198557456748776971215).testBit r.val = true := by decide

theorem even22_b21_s3_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (48000000 + (i : ZMod 443)) + 21))) = true) :
    (9897737545394987958529492030541029962965146887423642170050110439507306289576801415006824567926880521678256213173198557456748776971215).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_443_fin r
  change even22A443
    (-(33 * (46 * (48000000 + ((i % 443 : ℕ) : ZMod 443)) + 21))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 3873059591458812766741426108902430766822501499432625347777210124788499666793561585738608660509619508166012143938769518591) (.leaf 409 1311742570712801348227258946323951767256853705785639522093206391152415180536305004388446401942349970285085625979572401717247)) (.node (.leaf 419 1345827315416774877567828982974844659497902965606548691410909857571498065234147430191692231973172691737102112716252352884979711) (.leaf 421 5394216705013212217263000087350837417668891724487993692377083290793698991312426433622871120155042251563137661539354768294935539))) (.node (.node (.leaf 431 4687679424506659743238142993089425043353464239539951717486009664860729913650797906174079412428728227940017490306010477398690987991) (.leaf 433 22181352264518768394711863273574781322051236246474833661070517083085035023292167692089561844790763196489065878302759580196088575991)) (.node (.leaf 439 1419563475810072904056936606004676176897599537905814395301878414842783920618688801505092204393253075654825490565551763240775353081851) (.leaf 443 9897737545394987958529492030541029962965146887423642170050110439507306289576801415006824567926880521678256213173198557456748776971215))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
