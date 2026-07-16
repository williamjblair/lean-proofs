import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (0 + (r.val : ZMod 401)) + 29))) = true →
      (5164420932921576273280797669431127289126828766439317031662424419344216826334876229542278946181488391377988851623717232511).testBit r.val = true := by decide

theorem even22_b29_s0_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (0 + (i : ZMod 401)) + 29))) = true) :
    (5164420932921576273280797669431127289126828766439317031662424419344216826334876229542278946181488391377988851623717232511).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_401_fin r
  change even22A401
    (-(33 * (46 * (0 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (0 + (r.val : ZMod 409)) + 29))) = true →
      (1322091684910833729447431062023078036077903202529845792248055224924990495750090821167444959904944084149459578741315321462239).testBit r.val = true := by decide

theorem even22_b29_s0_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (0 + (i : ZMod 409)) + 29))) = true) :
    (1322091684910833729447431062023078036077903202529845792248055224924990495750090821167444959904944084149459578741315321462239).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_409_fin r
  change even22A409
    (-(33 * (46 * (0 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (0 + (r.val : ZMod 419)) + 29))) = true →
      (1353832168996482374795301473516933076094092501406859391564251084330171517727645382235796670752991743905782754193215584609468414).testBit r.val = true := by decide

theorem even22_b29_s0_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (0 + (i : ZMod 419)) + 29))) = true) :
    (1353832168996482374795301473516933076094092501406859391564251084330171517727645382235796670752991743905782754193215584609468414).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_419_fin r
  change even22A419
    (-(33 * (46 * (0 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (0 + (r.val : ZMod 421)) + 29))) = true →
      (1352520512125147611569079418597763655780735325813635558594788255216093482296000879288920072245092818248596205516645551373770687).testBit r.val = true := by decide

theorem even22_b29_s0_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (0 + (i : ZMod 421)) + 29))) = true) :
    (1352520512125147611569079418597763655780735325813635558594788255216093482296000879288920072245092818248596205516645551373770687).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_421_fin r
  change even22A421
    (-(33 * (46 * (0 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (0 + (r.val : ZMod 431)) + 29))) = true →
      (4145444961146874606543745643161391962768957776115905935050079801383223651878949717870430695394555764236901044265776526509155024895).testBit r.val = true := by decide

theorem even22_b29_s0_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (0 + (i : ZMod 431)) + 29))) = true) :
    (4145444961146874606543745643161391962768957776115905935050079801383223651878949717870430695394555764236901044265776526509155024895).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_431_fin r
  change even22A431
    (-(33 * (46 * (0 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (0 + (r.val : ZMod 433)) + 29))) = true →
      (22180677987429257746457807154470707285230877999264072773663534003953386760762182456647848243953079325872862976962629648942689680383).testBit r.val = true := by decide

theorem even22_b29_s0_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (0 + (i : ZMod 433)) + 29))) = true) :
    (22180677987429257746457807154470707285230877999264072773663534003953386760762182456647848243953079325872862976962629648942689680383).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_433_fin r
  change even22A433
    (-(33 * (46 * (0 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (0 + (r.val : ZMod 439)) + 29))) = true →
      (1400198005146887444872502999084868599912854258904968511495355697654915929380151387200321813088532538652694022643850975421809947049983).testBit r.val = true := by decide

theorem even22_b29_s0_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (0 + (i : ZMod 439)) + 29))) = true) :
    (1400198005146887444872502999084868599912854258904968511495355697654915929380151387200321813088532538652694022643850975421809947049983).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_439_fin r
  change even22A439
    (-(33 * (46 * (0 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (0 + (r.val : ZMod 443)) + 29))) = true →
      (20578754469723204736113642847165107555696665615970348288568117077271203588480283641649482610202411550472326337595965954464547566696683).testBit r.val = true := by decide

theorem even22_b29_s0_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (0 + (i : ZMod 443)) + 29))) = true) :
    (20578754469723204736113642847165107555696665615970348288568117077271203588480283641649482610202411550472326337595965954464547566696683).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_443_fin r
  change even22A443
    (-(33 * (46 * (0 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5164420932921576273280797669431127289126828766439317031662424419344216826334876229542278946181488391377988851623717232511) (.leaf 409 1322091684910833729447431062023078036077903202529845792248055224924990495750090821167444959904944084149459578741315321462239)) (.node (.leaf 419 1353832168996482374795301473516933076094092501406859391564251084330171517727645382235796670752991743905782754193215584609468414) (.leaf 421 1352520512125147611569079418597763655780735325813635558594788255216093482296000879288920072245092818248596205516645551373770687))) (.node (.node (.leaf 431 4145444961146874606543745643161391962768957776115905935050079801383223651878949717870430695394555764236901044265776526509155024895) (.leaf 433 22180677987429257746457807154470707285230877999264072773663534003953386760762182456647848243953079325872862976962629648942689680383)) (.node (.leaf 439 1400198005146887444872502999084868599912854258904968511495355697654915929380151387200321813088532538652694022643850975421809947049983) (.leaf 443 20578754469723204736113642847165107555696665615970348288568117077271203588480283641649482610202411550472326337595965954464547566696683))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
