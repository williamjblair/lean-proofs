import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s5_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (80000000 + (r.val : ZMod 499)) + 29))) = true →
      (1088266518625481073890415591919899672030873919286102852106343947471297404041832294439643699194812944811179449739321519329155894652298390709606606171871).testBit r.val = true := by decide

theorem even22_b29_s5_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (80000000 + (i : ZMod 499)) + 29))) = true) :
    (1088266518625481073890415591919899672030873919286102852106343947471297404041832294439643699194812944811179449739321519329155894652298390709606606171871).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_499_fin r
  change even22A499
    (-(33 * (46 * (80000000 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (80000000 + (r.val : ZMod 503)) + 29))) = true →
      (26161549450397085884650313097284557093008401884230831301511403033141008907077307395821459221903171736947528798384999111047674744402629924238614869045055).testBit r.val = true := by decide

theorem even22_b29_s5_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (80000000 + (i : ZMod 503)) + 29))) = true) :
    (26161549450397085884650313097284557093008401884230831301511403033141008907077307395821459221903171736947528798384999111047674744402629924238614869045055).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_503_fin r
  change even22A503
    (-(33 * (46 * (80000000 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (80000000 + (r.val : ZMod 509)) + 29))) = true →
      (1580638010982752684165425055662620380245991888992351742653274975124070594844205142467534119864481727422008463878837752409594959620307879527959266125143676).testBit r.val = true := by decide

theorem even22_b29_s5_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (80000000 + (i : ZMod 509)) + 29))) = true) :
    (1580638010982752684165425055662620380245991888992351742653274975124070594844205142467534119864481727422008463878837752409594959620307879527959266125143676).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_509_fin r
  change even22A509
    (-(33 * (46 * (80000000 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (80000000 + (r.val : ZMod 521)) + 29))) = true →
      (6863671562410970378583258038605571112418393053234410056095959738812129363384058454105798732115529870217975677868736421982013346306361350731619471541770613723).testBit r.val = true := by decide

theorem even22_b29_s5_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (80000000 + (i : ZMod 521)) + 29))) = true) :
    (6863671562410970378583258038605571112418393053234410056095959738812129363384058454105798732115529870217975677868736421982013346306361350731619471541770613723).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_521_fin r
  change even22A521
    (-(33 * (46 * (80000000 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (80000000 + (r.val : ZMod 523)) + 29))) = true →
      (27410377737029728795346666881368127988852144430036393576920729137433991725975102258227042615196085980260912246113138927035068095825909152736592549547197071327).testBit r.val = true := by decide

theorem even22_b29_s5_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (80000000 + (i : ZMod 523)) + 29))) = true) :
    (27410377737029728795346666881368127988852144430036393576920729137433991725975102258227042615196085980260912246113138927035068095825909152736592549547197071327).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_523_fin r
  change even22A523
    (-(33 * (46 * (80000000 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (80000000 + (r.val : ZMod 541)) + 29))) = true →
      (6225313492608249079643286013368408690418342249383282245752573002253747023621957817276794547965852203955396354210863477826146741581590334638268553972122927497078755).testBit r.val = true := by decide

theorem even22_b29_s5_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (80000000 + (i : ZMod 541)) + 29))) = true) :
    (6225313492608249079643286013368408690418342249383282245752573002253747023621957817276794547965852203955396354210863477826146741581590334638268553972122927497078755).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_541_fin r
  change even22A541
    (-(33 * (46 * (80000000 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (80000000 + (r.val : ZMod 547)) + 29))) = true →
      (460576294324744863568410402256031226873653639694996747744920521125493337399466753882120908656991115325928184163224682742197517170143844735257502824696226477709705203).testBit r.val = true := by decide

theorem even22_b29_s5_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (80000000 + (i : ZMod 547)) + 29))) = true) :
    (460576294324744863568410402256031226873653639694996747744920521125493337399466753882120908656991115325928184163224682742197517170143844735257502824696226477709705203).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_547_fin r
  change even22A547
    (-(33 * (46 * (80000000 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (80000000 + (r.val : ZMod 557)) + 29))) = true →
      (412302053957023642067850247854564220898803662060467763695035499203207730237099682341968335533161624624783742899645463093356034839094324987286949138260136981269768036207).testBit r.val = true := by decide

theorem even22_b29_s5_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (80000000 + (i : ZMod 557)) + 29))) = true) :
    (412302053957023642067850247854564220898803662060467763695035499203207730237099682341968335533161624624783742899645463093356034839094324987286949138260136981269768036207).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_557_fin r
  change even22A557
    (-(33 * (46 * (80000000 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S5Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1088266518625481073890415591919899672030873919286102852106343947471297404041832294439643699194812944811179449739321519329155894652298390709606606171871) (.leaf 503 26161549450397085884650313097284557093008401884230831301511403033141008907077307395821459221903171736947528798384999111047674744402629924238614869045055)) (.node (.leaf 509 1580638010982752684165425055662620380245991888992351742653274975124070594844205142467534119864481727422008463878837752409594959620307879527959266125143676) (.leaf 521 6863671562410970378583258038605571112418393053234410056095959738812129363384058454105798732115529870217975677868736421982013346306361350731619471541770613723))) (.node (.node (.leaf 523 27410377737029728795346666881368127988852144430036393576920729137433991725975102258227042615196085980260912246113138927035068095825909152736592549547197071327) (.leaf 541 6225313492608249079643286013368408690418342249383282245752573002253747023621957817276794547965852203955396354210863477826146741581590334638268553972122927497078755)) (.node (.leaf 547 460576294324744863568410402256031226873653639694996747744920521125493337399466753882120908656991115325928184163224682742197517170143844735257502824696226477709705203) (.leaf 557 412302053957023642067850247854564220898803662060467763695035499203207730237099682341968335533161624624783742899645463093356034839094324987286949138260136981269768036207))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S5Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S5Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
