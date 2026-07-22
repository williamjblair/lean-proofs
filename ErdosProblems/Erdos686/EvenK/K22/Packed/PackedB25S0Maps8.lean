import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (0 + (r.val : ZMod 499)) + 25))) = true →
      (1616909646379845882035046101066863470728536671654463752915077138399330226237294123928855610429226138601453027683628793106975247790772906336916546254847).testBit r.val = true := by decide

theorem even22_b25_s0_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (0 + (i : ZMod 499)) + 25))) = true) :
    (1616909646379845882035046101066863470728536671654463752915077138399330226237294123928855610429226138601453027683628793106975247790772906336916546254847).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_499_fin r
  change even22A499
    (-(33 * (46 * (0 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (0 + (r.val : ZMod 503)) + 25))) = true →
      (24958005041947767468697520880501679387950580773406344961204115438494294545389224464261308622335777124518000174495392156702903528309260783068119325206143).testBit r.val = true := by decide

theorem even22_b25_s0_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (0 + (i : ZMod 503)) + 25))) = true) :
    (24958005041947767468697520880501679387950580773406344961204115438494294545389224464261308622335777124518000174495392156702903528309260783068119325206143).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_503_fin r
  change even22A503
    (-(33 * (46 * (0 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (0 + (r.val : ZMod 509)) + 25))) = true →
      (1466450212903813591879274616949387642777457991973854394364362992818081949112915253040018759206381722363422199512920856751892813819280979741396632914587454).testBit r.val = true := by decide

theorem even22_b25_s0_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (0 + (i : ZMod 509)) + 25))) = true) :
    (1466450212903813591879274616949387642777457991973854394364362992818081949112915253040018759206381722363422199512920856751892813819280979741396632914587454).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_509_fin r
  change even22A509
    (-(33 * (46 * (0 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (0 + (r.val : ZMod 521)) + 25))) = true →
      (6864783645927069552260238931587823430668143071519701654710813229228873675977301788471624119884157351964000834600625387526760114232975470467476262411117772159).testBit r.val = true := by decide

theorem even22_b25_s0_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (0 + (i : ZMod 521)) + 25))) = true) :
    (6864783645927069552260238931587823430668143071519701654710813229228873675977301788471624119884157351964000834600625387526760114232975470467476262411117772159).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_521_fin r
  change even22A521
    (-(33 * (46 * (0 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (0 + (r.val : ZMod 523)) + 25))) = true →
      (4933968104509771588976419876227588387144389371434509162260015581906993668886771347467826936765823039986819051480513628155043182889332496468143082251447402494).testBit r.val = true := by decide

theorem even22_b25_s0_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (0 + (i : ZMod 523)) + 25))) = true) :
    (4933968104509771588976419876227588387144389371434509162260015581906993668886771347467826936765823039986819051480513628155043182889332496468143082251447402494).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_523_fin r
  change even22A523
    (-(33 * (46 * (0 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (0 + (r.val : ZMod 541)) + 25))) = true →
      (7198014720570487029711010111474025638807648478444472088549035263280312798530324819467306960500393394908819564239345416226835203480974815428383930614770882409789935).testBit r.val = true := by decide

theorem even22_b25_s0_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (0 + (i : ZMod 541)) + 25))) = true) :
    (7198014720570487029711010111474025638807648478444472088549035263280312798530324819467306960500393394908819564239345416226835203480974815428383930614770882409789935).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_541_fin r
  change even22A541
    (-(33 * (46 * (0 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (0 + (r.val : ZMod 547)) + 25))) = true →
      (402990202971630296940070930254185970802479716764373027356906408693797767315598540728977914032361386801528250192221491980483239196115373686581979903735355338708221951).testBit r.val = true := by decide

theorem even22_b25_s0_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (0 + (i : ZMod 547)) + 25))) = true) :
    (402990202971630296940070930254185970802479716764373027356906408693797767315598540728977914032361386801528250192221491980483239196115373686581979903735355338708221951).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_547_fin r
  change even22A547
    (-(33 * (46 * (0 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (0 + (r.val : ZMod 557)) + 25))) = true →
      (294610413349591510881149087023423524543912834816673924123163525382402459318122849988597260383028275392003294046460304163454448756792955054616342722334072294747194522525).testBit r.val = true := by decide

theorem even22_b25_s0_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (0 + (i : ZMod 557)) + 25))) = true) :
    (294610413349591510881149087023423524543912834816673924123163525382402459318122849988597260383028275392003294046460304163454448756792955054616342722334072294747194522525).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_557_fin r
  change even22A557
    (-(33 * (46 * (0 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1616909646379845882035046101066863470728536671654463752915077138399330226237294123928855610429226138601453027683628793106975247790772906336916546254847) (.leaf 503 24958005041947767468697520880501679387950580773406344961204115438494294545389224464261308622335777124518000174495392156702903528309260783068119325206143)) (.node (.leaf 509 1466450212903813591879274616949387642777457991973854394364362992818081949112915253040018759206381722363422199512920856751892813819280979741396632914587454) (.leaf 521 6864783645927069552260238931587823430668143071519701654710813229228873675977301788471624119884157351964000834600625387526760114232975470467476262411117772159))) (.node (.node (.leaf 523 4933968104509771588976419876227588387144389371434509162260015581906993668886771347467826936765823039986819051480513628155043182889332496468143082251447402494) (.leaf 541 7198014720570487029711010111474025638807648478444472088549035263280312798530324819467306960500393394908819564239345416226835203480974815428383930614770882409789935)) (.node (.leaf 547 402990202971630296940070930254185970802479716764373027356906408693797767315598540728977914032361386801528250192221491980483239196115373686581979903735355338708221951) (.leaf 557 294610413349591510881149087023423524543912834816673924123163525382402459318122849988597260383028275392003294046460304163454448756792955054616342722334072294747194522525))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
