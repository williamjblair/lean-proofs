import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s0_map_563_fin : ∀ r : Fin 563,
    even22A563 (-(33 * (46 * (0 + (r.val : ZMod 563)) + 21))) = true →
      (17425056142045217838930356104871001445782345884782112159495190179599355654564726674613937458109714706920246979145927558726719828368302880767225812869052857438167095050111).testBit r.val = true := by decide

theorem even22_b21_s0_map_563 (i : ℕ)
    (h : even22A563 (-(33 * (46 * (0 + (i : ZMod 563)) + 21))) = true) :
    (17425056142045217838930356104871001445782345884782112159495190179599355654564726674613937458109714706920246979145927558726719828368302880767225812869052857438167095050111).testBit (i % 563) = true := by
  let r : Fin 563 := ⟨i % 563, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_563_fin r
  change even22A563
    (-(33 * (46 * (0 + ((i % 563 : ℕ) : ZMod 563)) + 21))) = true
  have hcast : (i : ZMod 563) = ((i % 563 : ℕ) : ZMod 563) :=
    (ZMod.natCast_mod i 563).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_569_fin : ∀ r : Fin 569,
    even22A569 (-(33 * (46 * (0 + (r.val : ZMod 569)) + 21))) = true →
      (1923541473401228070080809378173419661191323980360967143617224580985419294992060263021537958409094040647421363708488512211131749601592593867703010851797802487473034105389055).testBit r.val = true := by decide

theorem even22_b21_s0_map_569 (i : ℕ)
    (h : even22A569 (-(33 * (46 * (0 + (i : ZMod 569)) + 21))) = true) :
    (1923541473401228070080809378173419661191323980360967143617224580985419294992060263021537958409094040647421363708488512211131749601592593867703010851797802487473034105389055).testBit (i % 569) = true := by
  let r : Fin 569 := ⟨i % 569, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_569_fin r
  change even22A569
    (-(33 * (46 * (0 + ((i % 569 : ℕ) : ZMod 569)) + 21))) = true
  have hcast : (i : ZMod 569) = ((i % 569 : ℕ) : ZMod 569) :=
    (ZMod.natCast_mod i 569).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_571_fin : ∀ r : Fin 571,
    even22A571 (-(33 * (46 * (0 + (r.val : ZMod 571)) + 21))) = true →
      (7727945427941176050834260945242480710835026629062976571277141622578686183170584864228837264418159915044498711028016726410528156064430658260966392825266391153017602644375487).testBit r.val = true := by decide

theorem even22_b21_s0_map_571 (i : ℕ)
    (h : even22A571 (-(33 * (46 * (0 + (i : ZMod 571)) + 21))) = true) :
    (7727945427941176050834260945242480710835026629062976571277141622578686183170584864228837264418159915044498711028016726410528156064430658260966392825266391153017602644375487).testBit (i % 571) = true := by
  let r : Fin 571 := ⟨i % 571, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_571_fin r
  change even22A571
    (-(33 * (46 * (0 + ((i % 571 : ℕ) : ZMod 571)) + 21))) = true
  have hcast : (i : ZMod 571) = ((i % 571 : ℕ) : ZMod 571) :=
    (ZMod.natCast_mod i 571).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_577_fin : ∀ r : Fin 577,
    even22A577 (-(33 * (46 * (0 + (r.val : ZMod 577)) + 21))) = true →
      (492666263746528361470806210778198414403755024020924981815440187422531534219732994826548731144697070429638913059876721623290647655386828315901793032921725753881300508654092159).testBit r.val = true := by decide

theorem even22_b21_s0_map_577 (i : ℕ)
    (h : even22A577 (-(33 * (46 * (0 + (i : ZMod 577)) + 21))) = true) :
    (492666263746528361470806210778198414403755024020924981815440187422531534219732994826548731144697070429638913059876721623290647655386828315901793032921725753881300508654092159).testBit (i % 577) = true := by
  let r : Fin 577 := ⟨i % 577, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_577_fin r
  change even22A577
    (-(33 * (46 * (0 + ((i % 577 : ℕ) : ZMod 577)) + 21))) = true
  have hcast : (i : ZMod 577) = ((i % 577 : ℕ) : ZMod 577) :=
    (ZMod.natCast_mod i 577).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_587_fin : ∀ r : Fin 587,
    even22A587 (-(33 * (46 * (0 + (r.val : ZMod 587)) + 21))) = true →
      (497888654136849569518988663354894766966856172081113585997115383053332450216937958651538124448509211435936524047964562813390995434463673004950203232412556522798978540932230347647).testBit r.val = true := by decide

theorem even22_b21_s0_map_587 (i : ℕ)
    (h : even22A587 (-(33 * (46 * (0 + (i : ZMod 587)) + 21))) = true) :
    (497888654136849569518988663354894766966856172081113585997115383053332450216937958651538124448509211435936524047964562813390995434463673004950203232412556522798978540932230347647).testBit (i % 587) = true := by
  let r : Fin 587 := ⟨i % 587, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_587_fin r
  change even22A587
    (-(33 * (46 * (0 + ((i % 587 : ℕ) : ZMod 587)) + 21))) = true
  have hcast : (i : ZMod 587) = ((i % 587 : ℕ) : ZMod 587) :=
    (ZMod.natCast_mod i 587).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_593_fin : ∀ r : Fin 593,
    even22A593 (-(33 * (46 * (0 + (r.val : ZMod 593)) + 21))) = true →
      (31272369719669022419029880939850119008400083445988400814248202424945409393331161040926124562660243573824659361229819869875726802864235132458108844583458933496665433273269681651711).testBit r.val = true := by decide

theorem even22_b21_s0_map_593 (i : ℕ)
    (h : even22A593 (-(33 * (46 * (0 + (i : ZMod 593)) + 21))) = true) :
    (31272369719669022419029880939850119008400083445988400814248202424945409393331161040926124562660243573824659361229819869875726802864235132458108844583458933496665433273269681651711).testBit (i % 593) = true := by
  let r : Fin 593 := ⟨i % 593, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_593_fin r
  change even22A593
    (-(33 * (46 * (0 + ((i % 593 : ℕ) : ZMod 593)) + 21))) = true
  have hcast : (i : ZMod 593) = ((i % 593 : ℕ) : ZMod 593) :=
    (ZMod.natCast_mod i 593).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_599_fin : ∀ r : Fin 599,
    even22A599 (-(33 * (46 * (0 + (r.val : ZMod 599)) + 21))) = true →
      (2073744591585852609245024031310276898405005508850910778773396003167756386054394419603038150467793639779889067796648139360193267907304114139192457270031249369668537487584033966450679).testBit r.val = true := by decide

theorem even22_b21_s0_map_599 (i : ℕ)
    (h : even22A599 (-(33 * (46 * (0 + (i : ZMod 599)) + 21))) = true) :
    (2073744591585852609245024031310276898405005508850910778773396003167756386054394419603038150467793639779889067796648139360193267907304114139192457270031249369668537487584033966450679).testBit (i % 599) = true := by
  let r : Fin 599 := ⟨i % 599, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_599_fin r
  change even22A599
    (-(33 * (46 * (0 + ((i % 599 : ℕ) : ZMod 599)) + 21))) = true
  have hcast : (i : ZMod 599) = ((i % 599 : ℕ) : ZMod 599) :=
    (ZMod.natCast_mod i 599).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_601_fin : ∀ r : Fin 601,
    even22A601 (-(33 * (46 * (0 + (r.val : ZMod 601)) + 21))) = true →
      (8160241110901116587906551131177342785521125317725666883714461513370191366249759184553269533654692735889345815775120819371204193045751127940026624927061770130522852991999294039883775).testBit r.val = true := by decide

theorem even22_b21_s0_map_601 (i : ℕ)
    (h : even22A601 (-(33 * (46 * (0 + (i : ZMod 601)) + 21))) = true) :
    (8160241110901116587906551131177342785521125317725666883714461513370191366249759184553269533654692735889345815775120819371204193045751127940026624927061770130522852991999294039883775).testBit (i % 601) = true := by
  let r : Fin 601 := ⟨i % 601, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_601_fin r
  change even22A601
    (-(33 * (46 * (0 + ((i % 601 : ℕ) : ZMod 601)) + 21))) = true
  have hcast : (i : ZMod 601) = ((i % 601 : ℕ) : ZMod 601) :=
    (ZMod.natCast_mod i 601).symm
  rw [← hcast]
  exact h

def even22PackedB21S0Group9Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 563 17425056142045217838930356104871001445782345884782112159495190179599355654564726674613937458109714706920246979145927558726719828368302880767225812869052857438167095050111) (.leaf 569 1923541473401228070080809378173419661191323980360967143617224580985419294992060263021537958409094040647421363708488512211131749601592593867703010851797802487473034105389055)) (.node (.leaf 571 7727945427941176050834260945242480710835026629062976571277141622578686183170584864228837264418159915044498711028016726410528156064430658260966392825266391153017602644375487) (.leaf 577 492666263746528361470806210778198414403755024020924981815440187422531534219732994826548731144697070429638913059876721623290647655386828315901793032921725753881300508654092159))) (.node (.node (.leaf 587 497888654136849569518988663354894766966856172081113585997115383053332450216937958651538124448509211435936524047964562813390995434463673004950203232412556522798978540932230347647) (.leaf 593 31272369719669022419029880939850119008400083445988400814248202424945409393331161040926124562660243573824659361229819869875726802864235132458108844583458933496665433273269681651711)) (.node (.leaf 599 2073744591585852609245024031310276898405005508850910778773396003167756386054394419603038150467793639779889067796648139360193267907304114139192457270031249369668537487584033966450679) (.leaf 601 8160241110901116587906551131177342785521125317725666883714461513370191366249759184553269533654692735889345815775120819371204193045751127940026624927061770130522852991999294039883775))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S0Group9TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S0Group9Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_563 i
          have hA := even22_allowed_int even22A563 even22_allowed_563 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_569 i
          have hA := even22_allowed_int even22A569 even22_allowed_569 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_571 i
          have hA := even22_allowed_int even22A571 even22_allowed_571 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_577 i
          have hA := even22_allowed_int even22A577 even22_allowed_577 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_587 i
          have hA := even22_allowed_int even22A587 even22_allowed_587 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_593 i
          have hA := even22_allowed_int even22A593 even22_allowed_593 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_599 i
          have hA := even22_allowed_int even22A599 even22_allowed_599 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_601 i
          have hA := even22_allowed_int even22A601 even22_allowed_601 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
