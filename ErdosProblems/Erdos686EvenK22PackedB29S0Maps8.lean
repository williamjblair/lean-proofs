import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (0 + (r.val : ZMod 499)) + 29))) = true →
      (1406534814953884918316294396702268886405866091080901624503626781395186335913113004592101665280062128210702605567670722436304543255968680660787365920694).testBit r.val = true := by decide

theorem even22_b29_s0_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (0 + (i : ZMod 499)) + 29))) = true) :
    (1406534814953884918316294396702268886405866091080901624503626781395186335913113004592101665280062128210702605567670722436304543255968680660787365920694).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_499_fin r
  change even22A499
    (-(33 * (46 * (0 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (0 + (r.val : ZMod 503)) + 29))) = true →
      (26072044722895450440818710148120677594314041312156189372454474013709270900367108336983191189339472459777471808713730250639888333621011621481689474128255).testBit r.val = true := by decide

theorem even22_b29_s0_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (0 + (i : ZMod 503)) + 29))) = true) :
    (26072044722895450440818710148120677594314041312156189372454474013709270900367108336983191189339472459777471808713730250639888333621011621481689474128255).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_503_fin r
  change even22A503
    (-(33 * (46 * (0 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (0 + (r.val : ZMod 509)) + 29))) = true →
      (1610482579566814336059842496562465977353240439218913978417550808377161684742971124833561648384709761310726020819300216255801706112194388702697250206187517).testBit r.val = true := by decide

theorem even22_b29_s0_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (0 + (i : ZMod 509)) + 29))) = true) :
    (1610482579566814336059842496562465977353240439218913978417550808377161684742971124833561648384709761310726020819300216255801706112194388702697250206187517).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_509_fin r
  change even22A509
    (-(33 * (46 * (0 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (0 + (r.val : ZMod 521)) + 29))) = true →
      (3432398777282682709801691608345713569761307591320986878933654730335051274093212699190060093956688694598831287221023325877663259106807749142767662154107516927).testBit r.val = true := by decide

theorem even22_b29_s0_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (0 + (i : ZMod 521)) + 29))) = true) :
    (3432398777282682709801691608345713569761307591320986878933654730335051274093212699190060093956688694598831287221023325877663259106807749142767662154107516927).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_521_fin r
  change even22A521
    (-(33 * (46 * (0 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (0 + (r.val : ZMod 523)) + 29))) = true →
      (27215964419781853126146140572220545399178357724052640560820024221935133872585516489753015228549185657770425364636690569412393384163152488946581207299968135159).testBit r.val = true := by decide

theorem even22_b29_s0_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (0 + (i : ZMod 523)) + 29))) = true) :
    (27215964419781853126146140572220545399178357724052640560820024221935133872585516489753015228549185657770425364636690569412393384163152488946581207299968135159).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_523_fin r
  change even22A523
    (-(33 * (46 * (0 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (0 + (r.val : ZMod 541)) + 29))) = true →
      (7191170679559856055413991445574805881408489541950698142847170182264401577359004108417876330259205507376786086853618974222171022955933306013525278923755050254691283).testBit r.val = true := by decide

theorem even22_b29_s0_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (0 + (i : ZMod 541)) + 29))) = true) :
    (7191170679559856055413991445574805881408489541950698142847170182264401577359004108417876330259205507376786086853618974222171022955933306013525278923755050254691283).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_541_fin r
  change even22A541
    (-(33 * (46 * (0 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (0 + (r.val : ZMod 547)) + 29))) = true →
      (459788989774661037572823751249260509729666810583366350282383756551403418817179730780205291330552823296222095374734022359162146114030529146559839648020030670058780670).testBit r.val = true := by decide

theorem even22_b29_s0_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (0 + (i : ZMod 547)) + 29))) = true) :
    (459788989774661037572823751249260509729666810583366350282383756551403418817179730780205291330552823296222095374734022359162146114030529146559839648020030670058780670).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_547_fin r
  change even22A547
    (-(33 * (46 * (0 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (0 + (r.val : ZMod 557)) + 29))) = true →
      (463222526975438570429834592862571268803568891099747323005772501565705842690815391148252914129692326156623144515994126139712004128927757208738316817454094000597414964223).testBit r.val = true := by decide

theorem even22_b29_s0_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (0 + (i : ZMod 557)) + 29))) = true) :
    (463222526975438570429834592862571268803568891099747323005772501565705842690815391148252914129692326156623144515994126139712004128927757208738316817454094000597414964223).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_557_fin r
  change even22A557
    (-(33 * (46 * (0 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1406534814953884918316294396702268886405866091080901624503626781395186335913113004592101665280062128210702605567670722436304543255968680660787365920694) (.leaf 503 26072044722895450440818710148120677594314041312156189372454474013709270900367108336983191189339472459777471808713730250639888333621011621481689474128255)) (.node (.leaf 509 1610482579566814336059842496562465977353240439218913978417550808377161684742971124833561648384709761310726020819300216255801706112194388702697250206187517) (.leaf 521 3432398777282682709801691608345713569761307591320986878933654730335051274093212699190060093956688694598831287221023325877663259106807749142767662154107516927))) (.node (.node (.leaf 523 27215964419781853126146140572220545399178357724052640560820024221935133872585516489753015228549185657770425364636690569412393384163152488946581207299968135159) (.leaf 541 7191170679559856055413991445574805881408489541950698142847170182264401577359004108417876330259205507376786086853618974222171022955933306013525278923755050254691283)) (.node (.leaf 547 459788989774661037572823751249260509729666810583366350282383756551403418817179730780205291330552823296222095374734022359162146114030529146559839648020030670058780670) (.leaf 557 463222526975438570429834592862571268803568891099747323005772501565705842690815391148252914129692326156623144515994126139712004128927757208738316817454094000597414964223))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
