import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s1_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (16000000 + (r.val : ZMod 499)) + 29))) = true →
      (1597123988811620829063497353719927365348752320287395111088508592750593554272250970416076174695500198627462713303477550709341867308603116147168828715007).testBit r.val = true := by decide

theorem even22_b29_s1_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (16000000 + (i : ZMod 499)) + 29))) = true) :
    (1597123988811620829063497353719927365348752320287395111088508592750593554272250970416076174695500198627462713303477550709341867308603116147168828715007).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_499_fin r
  change even22A499
    (-(33 * (46 * (16000000 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (16000000 + (r.val : ZMod 503)) + 29))) = true →
      (24448135306995877849151689418587793743110965232842368143614172058292549031177952584530363788541396062755359436133718444196836853177162522001670009757434).testBit r.val = true := by decide

theorem even22_b29_s1_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (16000000 + (i : ZMod 503)) + 29))) = true) :
    (24448135306995877849151689418587793743110965232842368143614172058292549031177952584530363788541396062755359436133718444196836853177162522001670009757434).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_503_fin r
  change even22A503
    (-(33 * (46 * (16000000 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (16000000 + (r.val : ZMod 509)) + 29))) = true →
      (1374205449574752189876903884582478811319666309924172768988403510126720951962019234828663973931898795235538853358223782466069646066280523664231257392651262).testBit r.val = true := by decide

theorem even22_b29_s1_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (16000000 + (i : ZMod 509)) + 29))) = true) :
    (1374205449574752189876903884582478811319666309924172768988403510126720951962019234828663973931898795235538853358223782466069646066280523664231257392651262).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_509_fin r
  change even22A509
    (-(33 * (46 * (16000000 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (16000000 + (r.val : ZMod 521)) + 29))) = true →
      (6006589920060279578220121238796106251949221940569413664271282031900210183353276027056870606971323734469440939455799061117488851873241291018935249502713411514).testBit r.val = true := by decide

theorem even22_b29_s1_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (16000000 + (i : ZMod 521)) + 29))) = true) :
    (6006589920060279578220121238796106251949221940569413664271282031900210183353276027056870606971323734469440939455799061117488851873241291018935249502713411514).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_521_fin r
  change even22A521
    (-(33 * (46 * (16000000 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (16000000 + (r.val : ZMod 523)) + 29))) = true →
      (27244665611344218239710574405821318379083970986033993136570195646451466484159295603305188081765627642643783539264119380390138959014897089712995095454771298301).testBit r.val = true := by decide

theorem even22_b29_s1_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (16000000 + (i : ZMod 523)) + 29))) = true) :
    (27244665611344218239710574405821318379083970986033993136570195646451466484159295603305188081765627642643783539264119380390138959014897089712995095454771298301).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_523_fin r
  change even22A523
    (-(33 * (46 * (16000000 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (16000000 + (r.val : ZMod 541)) + 29))) = true →
      (841734025272547302459665033768960993531819539570283992710878225019878688423913562381482869392812394551070289888055286715951664188316269536055682958449616774360822).testBit r.val = true := by decide

theorem even22_b29_s1_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (16000000 + (i : ZMod 541)) + 29))) = true) :
    (841734025272547302459665033768960993531819539570283992710878225019878688423913562381482869392812394551070289888055286715951664188316269536055682958449616774360822).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_541_fin r
  change even22A541
    (-(33 * (46 * (16000000 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (16000000 + (r.val : ZMod 547)) + 29))) = true →
      (428296479971350800995150531596417804396850214559167021334547187255303167418464654019043110857861072297387911178189599602982013016168797721100902523821802566753583093).testBit r.val = true := by decide

theorem even22_b29_s1_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (16000000 + (i : ZMod 547)) + 29))) = true) :
    (428296479971350800995150531596417804396850214559167021334547187255303167418464654019043110857861072297387911178189599602982013016168797721100902523821802566753583093).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_547_fin r
  change even22A547
    (-(33 * (46 * (16000000 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (16000000 + (r.val : ZMod 557)) + 29))) = true →
      (469884284959641753811696136735748722833370957095571425282845761350711821844839578182910967079322310671766442513691284651886102183340932219229205789132542570514799915006).testBit r.val = true := by decide

theorem even22_b29_s1_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (16000000 + (i : ZMod 557)) + 29))) = true) :
    (469884284959641753811696136735748722833370957095571425282845761350711821844839578182910967079322310671766442513691284651886102183340932219229205789132542570514799915006).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_557_fin r
  change even22A557
    (-(33 * (46 * (16000000 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S1Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1597123988811620829063497353719927365348752320287395111088508592750593554272250970416076174695500198627462713303477550709341867308603116147168828715007) (.leaf 503 24448135306995877849151689418587793743110965232842368143614172058292549031177952584530363788541396062755359436133718444196836853177162522001670009757434)) (.node (.leaf 509 1374205449574752189876903884582478811319666309924172768988403510126720951962019234828663973931898795235538853358223782466069646066280523664231257392651262) (.leaf 521 6006589920060279578220121238796106251949221940569413664271282031900210183353276027056870606971323734469440939455799061117488851873241291018935249502713411514))) (.node (.node (.leaf 523 27244665611344218239710574405821318379083970986033993136570195646451466484159295603305188081765627642643783539264119380390138959014897089712995095454771298301) (.leaf 541 841734025272547302459665033768960993531819539570283992710878225019878688423913562381482869392812394551070289888055286715951664188316269536055682958449616774360822)) (.node (.leaf 547 428296479971350800995150531596417804396850214559167021334547187255303167418464654019043110857861072297387911178189599602982013016168797721100902523821802566753583093) (.leaf 557 469884284959641753811696136735748722833370957095571425282845761350711821844839578182910967079322310671766442513691284651886102183340932219229205789132542570514799915006))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S1Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S1Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
