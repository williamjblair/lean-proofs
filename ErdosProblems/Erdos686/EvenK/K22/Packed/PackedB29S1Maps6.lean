import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s1_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (16000000 + (r.val : ZMod 401)) + 29))) = true →
      (4336015892222195571233222034756102694243320839008825362478966063435781492319518185300853640764339710255255078580686060539).testBit r.val = true := by decide

theorem even22_b29_s1_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (16000000 + (i : ZMod 401)) + 29))) = true) :
    (4336015892222195571233222034756102694243320839008825362478966063435781492319518185300853640764339710255255078580686060539).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_401_fin r
  change even22A401
    (-(33 * (46 * (16000000 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (16000000 + (r.val : ZMod 409)) + 29))) = true →
      (1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087).testBit r.val = true := by decide

theorem even22_b29_s1_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (16000000 + (i : ZMod 409)) + 29))) = true) :
    (1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_409_fin r
  change even22A409
    (-(33 * (46 * (16000000 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (16000000 + (r.val : ZMod 419)) + 29))) = true →
      (1331365389611863679187074849504196125769169288106714441007258299453636953966801093370346427048274451334623875211232168755830628).testBit r.val = true := by decide

theorem even22_b29_s1_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (16000000 + (i : ZMod 419)) + 29))) = true) :
    (1331365389611863679187074849504196125769169288106714441007258299453636953966801093370346427048274451334623875211232168755830628).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_419_fin r
  change even22A419
    (-(33 * (46 * (16000000 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (16000000 + (r.val : ZMod 421)) + 29))) = true →
      (4738448538726022801801452577202023323092691744274945652946494026380958305534164646992091240307200715408284376188431324661415935).testBit r.val = true := by decide

theorem even22_b29_s1_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (16000000 + (i : ZMod 421)) + 29))) = true) :
    (4738448538726022801801452577202023323092691744274945652946494026380958305534164646992091240307200715408284376188431324661415935).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_421_fin r
  change even22A421
    (-(33 * (46 * (16000000 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (16000000 + (r.val : ZMod 431)) + 29))) = true →
      (5372047511698006409104209761919926720693676889251640392560788724715620804664709047041679520907547248040585191893164545380427233259).testBit r.val = true := by decide

theorem even22_b29_s1_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (16000000 + (i : ZMod 431)) + 29))) = true) :
    (5372047511698006409104209761919926720693676889251640392560788724715620804664709047041679520907547248040585191893164545380427233259).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_431_fin r
  change even22A431
    (-(33 * (46 * (16000000 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (16000000 + (r.val : ZMod 433)) + 29))) = true →
      (22007388775751752906165171780216412598368465149774194791887578018125927664569691862199686723499693276794914215654094196509702340607).testBit r.val = true := by decide

theorem even22_b29_s1_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (16000000 + (i : ZMod 433)) + 29))) = true) :
    (22007388775751752906165171780216412598368465149774194791887578018125927664569691862199686723499693276794914215654094196509702340607).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_433_fin r
  change even22A433
    (-(33 * (46 * (16000000 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (16000000 + (r.val : ZMod 439)) + 29))) = true →
      (1330708159991602519415085607839931727877866664428058538773482420739003083079452496661098638253356162018382553197538011745951365980159).testBit r.val = true := by decide

theorem even22_b29_s1_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (16000000 + (i : ZMod 439)) + 29))) = true) :
    (1330708159991602519415085607839931727877866664428058538773482420739003083079452496661098638253356162018382553197538011745951365980159).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_439_fin r
  change even22A439
    (-(33 * (46 * (16000000 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (16000000 + (r.val : ZMod 443)) + 29))) = true →
      (17034583927319546847692492081697179376254913950382773282672752830061426378636492107304748551489438191901255893623638111546747664463611).testBit r.val = true := by decide

theorem even22_b29_s1_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (16000000 + (i : ZMod 443)) + 29))) = true) :
    (17034583927319546847692492081697179376254913950382773282672752830061426378636492107304748551489438191901255893623638111546747664463611).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_443_fin r
  change even22A443
    (-(33 * (46 * (16000000 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S1Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 4336015892222195571233222034756102694243320839008825362478966063435781492319518185300853640764339710255255078580686060539) (.leaf 409 1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087)) (.node (.leaf 419 1331365389611863679187074849504196125769169288106714441007258299453636953966801093370346427048274451334623875211232168755830628) (.leaf 421 4738448538726022801801452577202023323092691744274945652946494026380958305534164646992091240307200715408284376188431324661415935))) (.node (.node (.leaf 431 5372047511698006409104209761919926720693676889251640392560788724715620804664709047041679520907547248040585191893164545380427233259) (.leaf 433 22007388775751752906165171780216412598368465149774194791887578018125927664569691862199686723499693276794914215654094196509702340607)) (.node (.leaf 439 1330708159991602519415085607839931727877866664428058538773482420739003083079452496661098638253356162018382553197538011745951365980159) (.leaf 443 17034583927319546847692492081697179376254913950382773282672752830061426378636492107304748551489438191901255893623638111546747664463611))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S1Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S1Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
