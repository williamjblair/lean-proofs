import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s4_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (64000000 + (r.val : ZMod 449)) + 25))) = true →
      (1453621994520285781979779004364311380824203927148277592727672475546358004861689549330925658436416372066982659563193333889635036348284927).testBit r.val = true := by decide

theorem even22_b25_s4_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (64000000 + (i : ZMod 449)) + 25))) = true) :
    (1453621994520285781979779004364311380824203927148277592727672475546358004861689549330925658436416372066982659563193333889635036348284927).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_449_fin r
  change even22A449
    (-(33 * (46 * (64000000 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (64000000 + (r.val : ZMod 457)) + 25))) = true →
      (337253076564229617793133411517398295629582670930564283992817575141613994235963956327982064811056999464281484763993380856317946814691008511).testBit r.val = true := by decide

theorem even22_b25_s4_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (64000000 + (i : ZMod 457)) + 25))) = true) :
    (337253076564229617793133411517398295629582670930564283992817575141613994235963956327982064811056999464281484763993380856317946814691008511).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_457_fin r
  change even22A457
    (-(33 * (46 * (64000000 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (64000000 + (r.val : ZMod 461)) + 25))) = true →
      (5907563427356967174950053405546412821476080973976856436899592036235111354546447990175521339288125307600578341901029429864934297541025972223).testBit r.val = true := by decide

theorem even22_b25_s4_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (64000000 + (i : ZMod 461)) + 25))) = true) :
    (5907563427356967174950053405546412821476080973976856436899592036235111354546447990175521339288125307600578341901029429864934297541025972223).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_461_fin r
  change even22A461
    (-(33 * (46 * (64000000 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (64000000 + (r.val : ZMod 463)) + 25))) = true →
      (23443397876460140282365118475622009113123692386040254428728832995505945406462174720279055949213020678825755203990614031666879872430066626427).testBit r.val = true := by decide

theorem even22_b25_s4_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (64000000 + (i : ZMod 463)) + 25))) = true) :
    (23443397876460140282365118475622009113123692386040254428728832995505945406462174720279055949213020678825755203990614031666879872430066626427).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_463_fin r
  change even22A463
    (-(33 * (46 * (64000000 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (64000000 + (r.val : ZMod 467)) + 25))) = true →
      (368963503320594691725316824318941019401853542498269099739505766853552872076110490839889692819784695857036301249511585260870846944496252714873).testBit r.val = true := by decide

theorem even22_b25_s4_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (64000000 + (i : ZMod 467)) + 25))) = true) :
    (368963503320594691725316824318941019401853542498269099739505766853552872076110490839889692819784695857036301249511585260870846944496252714873).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_467_fin r
  change even22A467
    (-(33 * (46 * (64000000 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (64000000 + (r.val : ZMod 479)) + 25))) = true →
      (1108679271592455181219227126531259155946316346509339442175339747983193045206761446500836384065430536670629410522565753122349733319998363020558023).testBit r.val = true := by decide

theorem even22_b25_s4_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (64000000 + (i : ZMod 479)) + 25))) = true) :
    (1108679271592455181219227126531259155946316346509339442175339747983193045206761446500836384065430536670629410522565753122349733319998363020558023).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_479_fin r
  change even22A479
    (-(33 * (46 * (64000000 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (64000000 + (r.val : ZMod 487)) + 25))) = true →
      (374603704299633502890647025572641122346374761671940184730893191850227352491198220616304162485190015880540474929247000487049853790924318844353641399).testBit r.val = true := by decide

theorem even22_b25_s4_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (64000000 + (i : ZMod 487)) + 25))) = true) :
    (374603704299633502890647025572641122346374761671940184730893191850227352491198220616304162485190015880540474929247000487049853790924318844353641399).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_487_fin r
  change even22A487
    (-(33 * (46 * (64000000 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (64000000 + (r.val : ZMod 491)) + 25))) = true →
      (6330674337964112032460258023073816931324819769661497555081524773426425807850216374846891854721933409489655978103119858076817210949291838342658914875).testBit r.val = true := by decide

theorem even22_b25_s4_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (64000000 + (i : ZMod 491)) + 25))) = true) :
    (6330674337964112032460258023073816931324819769661497555081524773426425807850216374846891854721933409489655978103119858076817210949291838342658914875).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_491_fin r
  change even22A491
    (-(33 * (46 * (64000000 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S4Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453621994520285781979779004364311380824203927148277592727672475546358004861689549330925658436416372066982659563193333889635036348284927) (.leaf 457 337253076564229617793133411517398295629582670930564283992817575141613994235963956327982064811056999464281484763993380856317946814691008511)) (.node (.leaf 461 5907563427356967174950053405546412821476080973976856436899592036235111354546447990175521339288125307600578341901029429864934297541025972223) (.leaf 463 23443397876460140282365118475622009113123692386040254428728832995505945406462174720279055949213020678825755203990614031666879872430066626427))) (.node (.node (.leaf 467 368963503320594691725316824318941019401853542498269099739505766853552872076110490839889692819784695857036301249511585260870846944496252714873) (.leaf 479 1108679271592455181219227126531259155946316346509339442175339747983193045206761446500836384065430536670629410522565753122349733319998363020558023)) (.node (.leaf 487 374603704299633502890647025572641122346374761671940184730893191850227352491198220616304162485190015880540474929247000487049853790924318844353641399) (.leaf 491 6330674337964112032460258023073816931324819769661497555081524773426425807850216374846891854721933409489655978103119858076817210949291838342658914875))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S4Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S4Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
