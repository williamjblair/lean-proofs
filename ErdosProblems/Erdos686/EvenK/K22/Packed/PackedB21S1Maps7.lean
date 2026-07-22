import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (16000000 + (r.val : ZMod 449)) + 21))) = true →
      (1408241688651833120159447534213964976648028760783364868002491201439890503971674092035947550758654748819076351179586734988183892714845695).testBit r.val = true := by decide

theorem even22_b21_s1_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (16000000 + (i : ZMod 449)) + 21))) = true) :
    (1408241688651833120159447534213964976648028760783364868002491201439890503971674092035947550758654748819076351179586734988183892714845695).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_449_fin r
  change even22A449
    (-(33 * (46 * (16000000 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (16000000 + (r.val : ZMod 457)) + 21))) = true →
      (325620909270622799669047809343673018245290576454758130087272854903449511737712558890737722759148264643535646733945741913107023994491500531).testBit r.val = true := by decide

theorem even22_b21_s1_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (16000000 + (i : ZMod 457)) + 21))) = true) :
    (325620909270622799669047809343673018245290576454758130087272854903449511737712558890737722759148264643535646733945741913107023994491500531).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_457_fin r
  change even22A457
    (-(33 * (46 * (16000000 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (16000000 + (r.val : ZMod 461)) + 21))) = true →
      (5954171697322103879046498997001003691569955680438607565501747490659188867171751133799117004311246226983234161467204679837116828670129522687).testBit r.val = true := by decide

theorem even22_b21_s1_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (16000000 + (i : ZMod 461)) + 21))) = true) :
    (5954171697322103879046498997001003691569955680438607565501747490659188867171751133799117004311246226983234161467204679837116828670129522687).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_461_fin r
  change even22A461
    (-(33 * (46 * (16000000 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (16000000 + (r.val : ZMod 463)) + 21))) = true →
      (11860141197452644760556272576806181587254433036224957540902659606903419026895073350798311531369921717277110979881615339032239306602335563647).testBit r.val = true := by decide

theorem even22_b21_s1_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (16000000 + (i : ZMod 463)) + 21))) = true) :
    (11860141197452644760556272576806181587254433036224957540902659606903419026895073350798311531369921717277110979881615339032239306602335563647).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_463_fin r
  change even22A463
    (-(33 * (46 * (16000000 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (16000000 + (r.val : ZMod 467)) + 21))) = true →
      (357232499519011204229283962693434956165124890774209391496768686430675596602006531917080599148951743618197396954624439716313511075125780278491).testBit r.val = true := by decide

theorem even22_b21_s1_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (16000000 + (i : ZMod 467)) + 21))) = true) :
    (357232499519011204229283962693434956165124890774209391496768686430675596602006531917080599148951743618197396954624439716313511075125780278491).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_467_fin r
  change even22A467
    (-(33 * (46 * (16000000 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (16000000 + (r.val : ZMod 479)) + 21))) = true →
      (1560205837902382745401031270049976524723712948702756261578726806675509904067797549968278021585723147558938052883677031001098434583815522585655027).testBit r.val = true := by decide

theorem even22_b21_s1_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (16000000 + (i : ZMod 479)) + 21))) = true) :
    (1560205837902382745401031270049976524723712948702756261578726806675509904067797549968278021585723147558938052883677031001098434583815522585655027).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_479_fin r
  change even22A479
    (-(33 * (46 * (16000000 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (16000000 + (r.val : ZMod 487)) + 21))) = true →
      (398022555719737143849370111742898839082864185110002911932460429011509944208934205812364248440584634823058348896331795112052999479960508434413909982).testBit r.val = true := by decide

theorem even22_b21_s1_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (16000000 + (i : ZMod 487)) + 21))) = true) :
    (398022555719737143849370111742898839082864185110002911932460429011509944208934205812364248440584634823058348896331795112052999479960508434413909982).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_487_fin r
  change even22A487
    (-(33 * (46 * (16000000 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (16000000 + (r.val : ZMod 491)) + 21))) = true →
      (4693350349891882160561807963727912874474224185591905261337052586663594621098332214274873091303385506185322547088700277696022304336861955998131124598).testBit r.val = true := by decide

theorem even22_b21_s1_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (16000000 + (i : ZMod 491)) + 21))) = true) :
    (4693350349891882160561807963727912874474224185591905261337052586663594621098332214274873091303385506185322547088700277696022304336861955998131124598).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_491_fin r
  change even22A491
    (-(33 * (46 * (16000000 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1408241688651833120159447534213964976648028760783364868002491201439890503971674092035947550758654748819076351179586734988183892714845695) (.leaf 457 325620909270622799669047809343673018245290576454758130087272854903449511737712558890737722759148264643535646733945741913107023994491500531)) (.node (.leaf 461 5954171697322103879046498997001003691569955680438607565501747490659188867171751133799117004311246226983234161467204679837116828670129522687) (.leaf 463 11860141197452644760556272576806181587254433036224957540902659606903419026895073350798311531369921717277110979881615339032239306602335563647))) (.node (.node (.leaf 467 357232499519011204229283962693434956165124890774209391496768686430675596602006531917080599148951743618197396954624439716313511075125780278491) (.leaf 479 1560205837902382745401031270049976524723712948702756261578726806675509904067797549968278021585723147558938052883677031001098434583815522585655027)) (.node (.leaf 487 398022555719737143849370111742898839082864185110002911932460429011509944208934205812364248440584634823058348896331795112052999479960508434413909982) (.leaf 491 4693350349891882160561807963727912874474224185591905261337052586663594621098332214274873091303385506185322547088700277696022304336861955998131124598))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
