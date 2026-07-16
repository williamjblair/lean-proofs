import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s4_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (64000000 + (r.val : ZMod 401)) + 17))) = true →
      (5123519207104178929552863327031781332416828025649019998297179287919546970994908196296809088412964003637815627823695462399).testBit r.val = true := by decide

theorem even22_b17_s4_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (64000000 + (i : ZMod 401)) + 17))) = true) :
    (5123519207104178929552863327031781332416828025649019998297179287919546970994908196296809088412964003637815627823695462399).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_401_fin r
  change even22A401
    (-(33 * (46 * (64000000 + ((i % 401 : ℕ) : ZMod 401)) + 17))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (64000000 + (r.val : ZMod 409)) + 17))) = true →
      (1322111858776484768400906385670241464889304136519133703785071442209248831087529967911299918980829424741647398255840204420862).testBit r.val = true := by decide

theorem even22_b17_s4_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (64000000 + (i : ZMod 409)) + 17))) = true) :
    (1322111858776484768400906385670241464889304136519133703785071442209248831087529967911299918980829424741647398255840204420862).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_409_fin r
  change even22A409
    (-(33 * (46 * (64000000 + ((i % 409 : ℕ) : ZMod 409)) + 17))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (64000000 + (r.val : ZMod 419)) + 17))) = true →
      (1327313879952468799020077619709997568380969461740792383886852894141926884547199305317258317699983435509566095195155933417177087).testBit r.val = true := by decide

theorem even22_b17_s4_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (64000000 + (i : ZMod 419)) + 17))) = true) :
    (1327313879952468799020077619709997568380969461740792383886852894141926884547199305317258317699983435509566095195155933417177087).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_419_fin r
  change even22A419
    (-(33 * (46 * (64000000 + ((i % 419 : ℕ) : ZMod 419)) + 17))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (64000000 + (r.val : ZMod 421)) + 17))) = true →
      (2686324841710267168377626153167916846541192605009253304883412387417570392492964328598263865615342693733796417431978596175444990).testBit r.val = true := by decide

theorem even22_b17_s4_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (64000000 + (i : ZMod 421)) + 17))) = true) :
    (2686324841710267168377626153167916846541192605009253304883412387417570392492964328598263865615342693733796417431978596175444990).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_421_fin r
  change even22A421
    (-(33 * (46 * (64000000 + ((i % 421 : ℕ) : ZMod 421)) + 17))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (64000000 + (r.val : ZMod 431)) + 17))) = true →
      (5501995237051564955435602682235764522811024473286970306798478244884706100860923556521354771673391958547936651863544363566015287295).testBit r.val = true := by decide

theorem even22_b17_s4_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (64000000 + (i : ZMod 431)) + 17))) = true) :
    (5501995237051564955435602682235764522811024473286970306798478244884706100860923556521354771673391958547936651863544363566015287295).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_431_fin r
  change even22A431
    (-(33 * (46 * (64000000 + ((i % 431 : ℕ) : ZMod 431)) + 17))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (64000000 + (r.val : ZMod 433)) + 17))) = true →
      (22178649867718272135916811293361857242078194058776675171184220986966025616192311362440292379148161340266459280795103423550993723391).testBit r.val = true := by decide

theorem even22_b17_s4_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (64000000 + (i : ZMod 433)) + 17))) = true) :
    (22178649867718272135916811293361857242078194058776675171184220986966025616192311362440292379148161340266459280795103423550993723391).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_433_fin r
  change even22A433
    (-(33 * (46 * (64000000 + ((i % 433 : ℕ) : ZMod 433)) + 17))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (64000000 + (r.val : ZMod 439)) + 17))) = true →
      (1417180773609485987700192429381710074128630592131486889613294314322214837069439202521948760570721098319218015341190172107106666086399).testBit r.val = true := by decide

theorem even22_b17_s4_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (64000000 + (i : ZMod 439)) + 17))) = true) :
    (1417180773609485987700192429381710074128630592131486889613294314322214837069439202521948760570721098319218015341190172107106666086399).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_439_fin r
  change even22A439
    (-(33 * (46 * (64000000 + ((i % 439 : ℕ) : ZMod 439)) + 17))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (64000000 + (r.val : ZMod 443)) + 17))) = true →
      (17034589348626196472499346305422686300950521591550536709574297647577161949376495689531429323662747388961632320442564673563810177441766).testBit r.val = true := by decide

theorem even22_b17_s4_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (64000000 + (i : ZMod 443)) + 17))) = true) :
    (17034589348626196472499346305422686300950521591550536709574297647577161949376495689531429323662747388961632320442564673563810177441766).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_443_fin r
  change even22A443
    (-(33 * (46 * (64000000 + ((i % 443 : ℕ) : ZMod 443)) + 17))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB17S4Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5123519207104178929552863327031781332416828025649019998297179287919546970994908196296809088412964003637815627823695462399) (.leaf 409 1322111858776484768400906385670241464889304136519133703785071442209248831087529967911299918980829424741647398255840204420862)) (.node (.leaf 419 1327313879952468799020077619709997568380969461740792383886852894141926884547199305317258317699983435509566095195155933417177087) (.leaf 421 2686324841710267168377626153167916846541192605009253304883412387417570392492964328598263865615342693733796417431978596175444990))) (.node (.node (.leaf 431 5501995237051564955435602682235764522811024473286970306798478244884706100860923556521354771673391958547936651863544363566015287295) (.leaf 433 22178649867718272135916811293361857242078194058776675171184220986966025616192311362440292379148161340266459280795103423550993723391)) (.node (.leaf 439 1417180773609485987700192429381710074128630592131486889613294314322214837069439202521948760570721098319218015341190172107106666086399) (.leaf 443 17034589348626196472499346305422686300950521591550536709574297647577161949376495689531429323662747388961632320442564673563810177441766))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S4Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S4Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
