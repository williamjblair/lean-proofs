import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s1_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (16000000 + (r.val : ZMod 449)) + 17))) = true →
      (1402570907537140227385718292993800326055741793189900271919614808162326278444967894011013243115804258677641286352286673111119674319241206).testBit r.val = true := by decide

theorem even22_b17_s1_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (16000000 + (i : ZMod 449)) + 17))) = true) :
    (1402570907537140227385718292993800326055741793189900271919614808162326278444967894011013243115804258677641286352286673111119674319241206).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_449_fin r
  change even22A449
    (-(33 * (46 * (16000000 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (16000000 + (r.val : ZMod 457)) + 17))) = true →
      (186069293671992009399421610714490022920731530349247221854736932071222023313327203010734268258614885677321100915115934726079817179438383102).testBit r.val = true := by decide

theorem even22_b17_s1_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (16000000 + (i : ZMod 457)) + 17))) = true) :
    (186069293671992009399421610714490022920731530349247221854736932071222023313327203010734268258614885677321100915115934726079817179438383102).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_457_fin r
  change even22A457
    (-(33 * (46 * (16000000 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (16000000 + (r.val : ZMod 461)) + 17))) = true →
      (3721321561409614573162724092813727224371149356804690800644221437173620991211989446325525760223225647030226150038483022039104920663658250239).testBit r.val = true := by decide

theorem even22_b17_s1_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (16000000 + (i : ZMod 461)) + 17))) = true) :
    (3721321561409614573162724092813727224371149356804690800644221437173620991211989446325525760223225647030226150038483022039104920663658250239).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_461_fin r
  change even22A461
    (-(33 * (46 * (16000000 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (16000000 + (r.val : ZMod 463)) + 17))) = true →
      (23817005840292609846632481357482967769929051372819392257030521514419509150175853452356017641792860471618586337155023151851821680501301704191).testBit r.val = true := by decide

theorem even22_b17_s1_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (16000000 + (i : ZMod 463)) + 17))) = true) :
    (23817005840292609846632481357482967769929051372819392257030521514419509150175853452356017641792860471618586337155023151851821680501301704191).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_463_fin r
  change even22A463
    (-(33 * (46 * (16000000 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (16000000 + (r.val : ZMod 467)) + 17))) = true →
      (345158036016872155958871531530439842717380673126314499023509937173291195375011706328998230434796750229970887095939972708697488006379595879933).testBit r.val = true := by decide

theorem even22_b17_s1_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (16000000 + (i : ZMod 467)) + 17))) = true) :
    (345158036016872155958871531530439842717380673126314499023509937173291195375011706328998230434796750229970887095939972708697488006379595879933).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_467_fin r
  change even22A467
    (-(33 * (46 * (16000000 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (16000000 + (r.val : ZMod 479)) + 17))) = true →
      (1547870093446767297285532264695008236922530255060332035247589310500614521814477246510100635421563494578103615405219637444751262758770582906470135).testBit r.val = true := by decide

theorem even22_b17_s1_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (16000000 + (i : ZMod 479)) + 17))) = true) :
    (1547870093446767297285532264695008236922530255060332035247589310500614521814477246510100635421563494578103615405219637444751262758770582906470135).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_479_fin r
  change even22A479
    (-(33 * (46 * (16000000 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (16000000 + (r.val : ZMod 487)) + 17))) = true →
      (99894332562033681118191973367576525795670173009941809352783879311084837374510518306490975496184592341432517614722088873137960594299443892841348351).testBit r.val = true := by decide

theorem even22_b17_s1_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (16000000 + (i : ZMod 487)) + 17))) = true) :
    (99894332562033681118191973367576525795670173009941809352783879311084837374510518306490975496184592341432517614722088873137960594299443892841348351).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_487_fin r
  change even22A487
    (-(33 * (46 * (16000000 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (16000000 + (r.val : ZMod 491)) + 17))) = true →
      (6315236319121711948148958234114101774000785633844486306188673387056980907829268537593568064973174833084587552138371944218245648534519399436600848363).testBit r.val = true := by decide

theorem even22_b17_s1_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (16000000 + (i : ZMod 491)) + 17))) = true) :
    (6315236319121711948148958234114101774000785633844486306188673387056980907829268537593568064973174833084587552138371944218245648534519399436600848363).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_491_fin r
  change even22A491
    (-(33 * (46 * (16000000 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S1Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1402570907537140227385718292993800326055741793189900271919614808162326278444967894011013243115804258677641286352286673111119674319241206) (.leaf 457 186069293671992009399421610714490022920731530349247221854736932071222023313327203010734268258614885677321100915115934726079817179438383102)) (.node (.leaf 461 3721321561409614573162724092813727224371149356804690800644221437173620991211989446325525760223225647030226150038483022039104920663658250239) (.leaf 463 23817005840292609846632481357482967769929051372819392257030521514419509150175853452356017641792860471618586337155023151851821680501301704191))) (.node (.node (.leaf 467 345158036016872155958871531530439842717380673126314499023509937173291195375011706328998230434796750229970887095939972708697488006379595879933) (.leaf 479 1547870093446767297285532264695008236922530255060332035247589310500614521814477246510100635421563494578103615405219637444751262758770582906470135)) (.node (.leaf 487 99894332562033681118191973367576525795670173009941809352783879311084837374510518306490975496184592341432517614722088873137960594299443892841348351) (.leaf 491 6315236319121711948148958234114101774000785633844486306188673387056980907829268537593568064973174833084587552138371944218245648534519399436600848363))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S1Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S1Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
