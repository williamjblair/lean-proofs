import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (0 + (r.val : ZMod 401)) + 25))) = true →
      (3779991739566668204792129688197380506462871502731508213128049207634503870487324532473776329940585125998054443882473512731).testBit r.val = true := by decide

theorem even22_b25_s0_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (0 + (i : ZMod 401)) + 25))) = true) :
    (3779991739566668204792129688197380506462871502731508213128049207634503870487324532473776329940585125998054443882473512731).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_401_fin r
  change even22A401
    (-(33 * (46 * (0 + ((i % 401 : ℕ) : ZMod 401)) + 25))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (0 + (r.val : ZMod 409)) + 25))) = true →
      (658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423).testBit r.val = true := by decide

theorem even22_b25_s0_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (0 + (i : ZMod 409)) + 25))) = true) :
    (658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_409_fin r
  change even22A409
    (-(33 * (46 * (0 + ((i % 409 : ℕ) : ZMod 409)) + 25))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (0 + (r.val : ZMod 419)) + 25))) = true →
      (1352844785572946477947744556079729888525709535773599332068185385680394615998066251294979433686522700104952301182235093073649279).testBit r.val = true := by decide

theorem even22_b25_s0_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (0 + (i : ZMod 419)) + 25))) = true) :
    (1352844785572946477947744556079729888525709535773599332068185385680394615998066251294979433686522700104952301182235093073649279).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_419_fin r
  change even22A419
    (-(33 * (46 * (0 + ((i % 419 : ℕ) : ZMod 419)) + 25))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (0 + (r.val : ZMod 421)) + 25))) = true →
      (4738449133853933424674920971497871131117604242136200972755166775249645737198644020007023162573810252576706750646109507554246655).testBit r.val = true := by decide

theorem even22_b25_s0_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (0 + (i : ZMod 421)) + 25))) = true) :
    (4738449133853933424674920971497871131117604242136200972755166775249645737198644020007023162573810252576706750646109507554246655).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_421_fin r
  change even22A421
    (-(33 * (46 * (0 + ((i % 421 : ℕ) : ZMod 421)) + 25))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (0 + (r.val : ZMod 431)) + 25))) = true →
      (5415285218172966474158576274264475215637526727940302952163698149912439847631652351943905840258531663589366101535086729522870747131).testBit r.val = true := by decide

theorem even22_b25_s0_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (0 + (i : ZMod 431)) + 25))) = true) :
    (5415285218172966474158576274264475215637526727940302952163698149912439847631652351943905840258531663589366101535086729522870747131).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_431_fin r
  change even22A431
    (-(33 * (46 * (0 + ((i % 431 : ℕ) : ZMod 431)) + 25))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (0 + (r.val : ZMod 433)) + 25))) = true →
      (21488190108778316136412727699766828825439261317144876508585695970224909137684407807887027298072541287175523823195453974665035251703).testBit r.val = true := by decide

theorem even22_b25_s0_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (0 + (i : ZMod 433)) + 25))) = true) :
    (21488190108778316136412727699766828825439261317144876508585695970224909137684407807887027298072541287175523823195453974665035251703).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_433_fin r
  change even22A433
    (-(33 * (46 * (0 + ((i % 433 : ℕ) : ZMod 433)) + 25))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (0 + (r.val : ZMod 439)) + 25))) = true →
      (1419606846370359826951492972626215833259339345440464031751005119383100531116369737924743346759435757345763185414389033920833735357054).testBit r.val = true := by decide

theorem even22_b25_s0_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (0 + (i : ZMod 439)) + 25))) = true) :
    (1419606846370359826951492972626215833259339345440464031751005119383100531116369737924743346759435757345763185414389033920833735357054).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_439_fin r
  change even22A439
    (-(33 * (46 * (0 + ((i % 439 : ℕ) : ZMod 439)) + 25))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (0 + (r.val : ZMod 443)) + 25))) = true →
      (22533291649294593966228813058691700921557903325402009203884902170636259578055627855160527705102544402284186247340622330099330969362430).testBit r.val = true := by decide

theorem even22_b25_s0_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (0 + (i : ZMod 443)) + 25))) = true) :
    (22533291649294593966228813058691700921557903325402009203884902170636259578055627855160527705102544402284186247340622330099330969362430).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_443_fin r
  change even22A443
    (-(33 * (46 * (0 + ((i % 443 : ℕ) : ZMod 443)) + 25))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 3779991739566668204792129688197380506462871502731508213128049207634503870487324532473776329940585125998054443882473512731) (.leaf 409 658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423)) (.node (.leaf 419 1352844785572946477947744556079729888525709535773599332068185385680394615998066251294979433686522700104952301182235093073649279) (.leaf 421 4738449133853933424674920971497871131117604242136200972755166775249645737198644020007023162573810252576706750646109507554246655))) (.node (.node (.leaf 431 5415285218172966474158576274264475215637526727940302952163698149912439847631652351943905840258531663589366101535086729522870747131) (.leaf 433 21488190108778316136412727699766828825439261317144876508585695970224909137684407807887027298072541287175523823195453974665035251703)) (.node (.leaf 439 1419606846370359826951492972626215833259339345440464031751005119383100531116369737924743346759435757345763185414389033920833735357054) (.leaf 443 22533291649294593966228813058691700921557903325402009203884902170636259578055627855160527705102544402284186247340622330099330969362430))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
