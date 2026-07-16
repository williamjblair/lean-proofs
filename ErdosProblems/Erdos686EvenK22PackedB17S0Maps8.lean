import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (0 + (r.val : ZMod 499)) + 17))) = true →
      (703214416237696487140520119122424623468548391983788428210803120626611052782894333060792984556602611030261205057589764441896464900282735799669612347355).testBit r.val = true := by decide

theorem even22_b17_s0_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (0 + (i : ZMod 499)) + 17))) = true) :
    (703214416237696487140520119122424623468548391983788428210803120626611052782894333060792984556602611030261205057589764441896464900282735799669612347355).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_499_fin r
  change even22A499
    (-(33 * (46 * (0 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (0 + (r.val : ZMod 503)) + 17))) = true →
      (26044860488679735646151875905326573354108900250889538694999626417164216074982317818246965164514548596874695494108767343546300463157745671885896640625535).testBit r.val = true := by decide

theorem even22_b17_s0_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (0 + (i : ZMod 503)) + 17))) = true) :
    (26044860488679735646151875905326573354108900250889538694999626417164216074982317818246965164514548596874695494108767343546300463157745671885896640625535).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_503_fin r
  change even22A503
    (-(33 * (46 * (0 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (0 + (r.val : ZMod 509)) + 17))) = true →
      (1256969200506365023868926371435808308174463012869082900530701691017920288285026468407159051443563712082535232937035300976455275091205785606747532302450607).testBit r.val = true := by decide

theorem even22_b17_s0_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (0 + (i : ZMod 509)) + 17))) = true) :
    (1256969200506365023868926371435808308174463012869082900530701691017920288285026468407159051443563712082535232937035300976455275091205785606747532302450607).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_509_fin r
  change even22A509
    (-(33 * (46 * (0 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (0 + (r.val : ZMod 521)) + 17))) = true →
      (6863065115845045701131598884178322815752529907169433826475887075317740196268891317587060005388437388193044687743482560744143044785093725849271414453792931838).testBit r.val = true := by decide

theorem even22_b17_s0_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (0 + (i : ZMod 521)) + 17))) = true) :
    (6863065115845045701131598884178322815752529907169433826475887075317740196268891317587060005388437388193044687743482560744143044785093725849271414453792931838).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_521_fin r
  change even22A521
    (-(33 * (46 * (0 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (0 + (r.val : ZMod 523)) + 17))) = true →
      (25739429776408401872935234545417819094133700234648640878859931882499231116681551045618207712839012653762429765714414888616770061910793939963634559926252002751).testBit r.val = true := by decide

theorem even22_b17_s0_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (0 + (i : ZMod 523)) + 17))) = true) :
    (25739429776408401872935234545417819094133700234648640878859931882499231116681551045618207712839012653762429765714414888616770061910793939963634559926252002751).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_523_fin r
  change even22A523
    (-(33 * (46 * (0 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (0 + (r.val : ZMod 541)) + 17))) = true →
      (5731609206263790679512437741877662280227627070706578836878838554352386286906629287795082662997754993614406969519848615784683805857150273101085084645526679204593151).testBit r.val = true := by decide

theorem even22_b17_s0_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (0 + (i : ZMod 541)) + 17))) = true) :
    (5731609206263790679512437741877662280227627070706578836878838554352386286906629287795082662997754993614406969519848615784683805857150273101085084645526679204593151).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_541_fin r
  change even22A541
    (-(33 * (46 * (0 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (0 + (r.val : ZMod 547)) + 17))) = true →
      (230224444214099915373287995246015313696821285585136787148809573532059799983192870362045097438464620235723950165058771398511495962964996801443234605701778541002096383).testBit r.val = true := by decide

theorem even22_b17_s0_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (0 + (i : ZMod 547)) + 17))) = true) :
    (230224444214099915373287995246015313696821285585136787148809573532059799983192870362045097438464620235723950165058771398511495962964996801443234605701778541002096383).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_547_fin r
  change even22A547
    (-(33 * (46 * (0 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (0 + (r.val : ZMod 557)) + 17))) = true →
      (471456971823562901575510297357064914586759664209062221709145082989294619580538497288569667067809329126823136484085645922626307053603650181928144897329708631901901683423).testBit r.val = true := by decide

theorem even22_b17_s0_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (0 + (i : ZMod 557)) + 17))) = true) :
    (471456971823562901575510297357064914586759664209062221709145082989294619580538497288569667067809329126823136484085645922626307053603650181928144897329708631901901683423).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_557_fin r
  change even22A557
    (-(33 * (46 * (0 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 703214416237696487140520119122424623468548391983788428210803120626611052782894333060792984556602611030261205057589764441896464900282735799669612347355) (.leaf 503 26044860488679735646151875905326573354108900250889538694999626417164216074982317818246965164514548596874695494108767343546300463157745671885896640625535)) (.node (.leaf 509 1256969200506365023868926371435808308174463012869082900530701691017920288285026468407159051443563712082535232937035300976455275091205785606747532302450607) (.leaf 521 6863065115845045701131598884178322815752529907169433826475887075317740196268891317587060005388437388193044687743482560744143044785093725849271414453792931838))) (.node (.node (.leaf 523 25739429776408401872935234545417819094133700234648640878859931882499231116681551045618207712839012653762429765714414888616770061910793939963634559926252002751) (.leaf 541 5731609206263790679512437741877662280227627070706578836878838554352386286906629287795082662997754993614406969519848615784683805857150273101085084645526679204593151)) (.node (.leaf 547 230224444214099915373287995246015313696821285585136787148809573532059799983192870362045097438464620235723950165058771398511495962964996801443234605701778541002096383) (.leaf 557 471456971823562901575510297357064914586759664209062221709145082989294619580538497288569667067809329126823136484085645922626307053603650181928144897329708631901901683423))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
