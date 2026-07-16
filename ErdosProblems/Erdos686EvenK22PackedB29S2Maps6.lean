import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s2_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (32000000 + (r.val : ZMod 401)) + 29))) = true →
      (4841708363083155412126598693279344744420985941107294905232929341830682764833634374828960106722143059904534618780549986237).testBit r.val = true := by decide

theorem even22_b29_s2_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (32000000 + (i : ZMod 401)) + 29))) = true) :
    (4841708363083155412126598693279344744420985941107294905232929341830682764833634374828960106722143059904534618780549986237).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_401_fin r
  change even22A401
    (-(33 * (46 * (32000000 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (32000000 + (r.val : ZMod 409)) + 29))) = true →
      (1310486769672012357306304704756256077328990636170510582148257951372010472165498437816692121217302174369360169783456018792445).testBit r.val = true := by decide

theorem even22_b29_s2_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (32000000 + (i : ZMod 409)) + 29))) = true) :
    (1310486769672012357306304704756256077328990636170510582148257951372010472165498437816692121217302174369360169783456018792445).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_409_fin r
  change even22A409
    (-(33 * (46 * (32000000 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (32000000 + (r.val : ZMod 419)) + 29))) = true →
      (1353841004896386042254375001722017120969867492656101229602699495671288476945135511351859284646474369586869591490734648603967487).testBit r.val = true := by decide

theorem even22_b29_s2_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (32000000 + (i : ZMod 419)) + 29))) = true) :
    (1353841004896386042254375001722017120969867492656101229602699495671288476945135511351859284646474369586869591490734648603967487).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_419_fin r
  change even22A419
    (-(33 * (46 * (32000000 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (32000000 + (r.val : ZMod 421)) + 29))) = true →
      (4057561448016443797040449644824897252805361093185566472546837076348418324453973827595475455591813719068269957035379097668745199).testBit r.val = true := by decide

theorem even22_b29_s2_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (32000000 + (i : ZMod 421)) + 29))) = true) :
    (4057561448016443797040449644824897252805361093185566472546837076348418324453973827595475455591813719068269957035379097668745199).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_421_fin r
  change even22A421
    (-(33 * (46 * (32000000 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (32000000 + (r.val : ZMod 431)) + 29))) = true →
      (5545170132736681872253267297301322386344690535229047902470288516325476938017875721044810401931951542875374031329270830640010198783).testBit r.val = true := by decide

theorem even22_b29_s2_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (32000000 + (i : ZMod 431)) + 29))) = true) :
    (5545170132736681872253267297301322386344690535229047902470288516325476938017875721044810401931951542875374031329270830640010198783).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_431_fin r
  change even22A431
    (-(33 * (46 * (32000000 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (32000000 + (r.val : ZMod 433)) + 29))) = true →
      (22181017770197888311542560313807688456361187301135302687513685324435178611603593720483821746393097975325996332326929111787241471487).testBit r.val = true := by decide

theorem even22_b29_s2_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (32000000 + (i : ZMod 433)) + 29))) = true) :
    (22181017770197888311542560313807688456361187301135302687513685324435178611603593720483821746393097975325996332326929111787241471487).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_433_fin r
  change even22A433
    (-(33 * (46 * (32000000 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (32000000 + (r.val : ZMod 439)) + 29))) = true →
      (1419606205909366392421647873600285053435695553114010061649377009956848282763981577481903815261715830943343748357738412896015154937837).testBit r.val = true := by decide

theorem even22_b29_s2_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (32000000 + (i : ZMod 439)) + 29))) = true) :
    (1419606205909366392421647873600285053435695553114010061649377009956848282763981577481903815261715830943343748357738412896015154937837).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_439_fin r
  change even22A439
    (-(33 * (46 * (32000000 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (32000000 + (r.val : ZMod 443)) + 29))) = true →
      (22701145110265337564297494685827924767586249614301119182257676244774959649142363028778721936314625909116179185042351729277948466298807).testBit r.val = true := by decide

theorem even22_b29_s2_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (32000000 + (i : ZMod 443)) + 29))) = true) :
    (22701145110265337564297494685827924767586249614301119182257676244774959649142363028778721936314625909116179185042351729277948466298807).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_443_fin r
  change even22A443
    (-(33 * (46 * (32000000 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S2Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 4841708363083155412126598693279344744420985941107294905232929341830682764833634374828960106722143059904534618780549986237) (.leaf 409 1310486769672012357306304704756256077328990636170510582148257951372010472165498437816692121217302174369360169783456018792445)) (.node (.leaf 419 1353841004896386042254375001722017120969867492656101229602699495671288476945135511351859284646474369586869591490734648603967487) (.leaf 421 4057561448016443797040449644824897252805361093185566472546837076348418324453973827595475455591813719068269957035379097668745199))) (.node (.node (.leaf 431 5545170132736681872253267297301322386344690535229047902470288516325476938017875721044810401931951542875374031329270830640010198783) (.leaf 433 22181017770197888311542560313807688456361187301135302687513685324435178611603593720483821746393097975325996332326929111787241471487)) (.node (.leaf 439 1419606205909366392421647873600285053435695553114010061649377009956848282763981577481903815261715830943343748357738412896015154937837) (.leaf 443 22701145110265337564297494685827924767586249614301119182257676244774959649142363028778721936314625909116179185042351729277948466298807))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S2Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S2Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
