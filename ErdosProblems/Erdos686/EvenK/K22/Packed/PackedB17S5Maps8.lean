import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s5_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (80000000 + (r.val : ZMod 499)) + 17))) = true →
      (1225694864837316577654601719129168058244790421050138058025436256538275488530124237293779859882364535132657150946224430133325478560222436963139183439355).testBit r.val = true := by decide

theorem even22_b17_s5_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (80000000 + (i : ZMod 499)) + 17))) = true) :
    (1225694864837316577654601719129168058244790421050138058025436256538275488530124237293779859882364535132657150946224430133325478560222436963139183439355).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_499_fin r
  change even22A499
    (-(33 * (46 * (80000000 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (80000000 + (r.val : ZMod 503)) + 17))) = true →
      (19601978625903071957686369332989608667416603321735128969312593305032477640067567390948933313386436060497408096789045308489842138007869744154432934445055).testBit r.val = true := by decide

theorem even22_b17_s5_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (80000000 + (i : ZMod 503)) + 17))) = true) :
    (19601978625903071957686369332989608667416603321735128969312593305032477640067567390948933313386436060497408096789045308489842138007869744154432934445055).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_503_fin r
  change even22A503
    (-(33 * (46 * (80000000 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (80000000 + (r.val : ZMod 509)) + 17))) = true →
      (1569180822675272775687990097345583068420810673089573124145795657558392384179986841116886124351241708958971609585791004706270610353296897023703725870413823).testBit r.val = true := by decide

theorem even22_b17_s5_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (80000000 + (i : ZMod 509)) + 17))) = true) :
    (1569180822675272775687990097345583068420810673089573124145795657558392384179986841116886124351241708958971609585791004706270610353296897023703725870413823).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_509_fin r
  change even22A509
    (-(33 * (46 * (80000000 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (80000000 + (r.val : ZMod 521)) + 17))) = true →
      (6435687143155293079743346895427384392279065921563614275956500155204231160230788109381032082096639931526583524820772926933676745575683881675087514681302668285).testBit r.val = true := by decide

theorem even22_b17_s5_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (80000000 + (i : ZMod 521)) + 17))) = true) :
    (6435687143155293079743346895427384392279065921563614275956500155204231160230788109381032082096639931526583524820772926933676745575683881675087514681302668285).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_521_fin r
  change even22A521
    (-(33 * (46 * (80000000 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (80000000 + (r.val : ZMod 523)) + 17))) = true →
      (26597279935541293941327324261486377073480424748290028357024653134356044408622667767297340333623742085610173500894273155687976839079078873842547338936124949951).testBit r.val = true := by decide

theorem even22_b17_s5_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (80000000 + (i : ZMod 523)) + 17))) = true) :
    (26597279935541293941327324261486377073480424748290028357024653134356044408622667767297340333623742085610173500894273155687976839079078873842547338936124949951).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_523_fin r
  change even22A523
    (-(33 * (46 * (80000000 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (80000000 + (r.val : ZMod 541)) + 17))) = true →
      (7197050434482100320131610573067616512780153418686098100524511978027121681408594708158672281306046449328994575459483727708289943473331872296128117320551455732037565).testBit r.val = true := by decide

theorem even22_b17_s5_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (80000000 + (i : ZMod 541)) + 17))) = true) :
    (7197050434482100320131610573067616512780153418686098100524511978027121681408594708158672281306046449328994575459483727708289943473331872296128117320551455732037565).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_541_fin r
  change even22A541
    (-(33 * (46 * (80000000 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (80000000 + (r.val : ZMod 547)) + 17))) = true →
      (381507882899057585189284451217128351597520980450446817894702084738802916823457023568085716493352359381576886426556267466970248458945923371542742987032177999800663895).testBit r.val = true := by decide

theorem even22_b17_s5_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (80000000 + (i : ZMod 547)) + 17))) = true) :
    (381507882899057585189284451217128351597520980450446817894702084738802916823457023568085716493352359381576886426556267466970248458945923371542742987032177999800663895).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_547_fin r
  change even22A547
    (-(33 * (46 * (80000000 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (80000000 + (r.val : ZMod 557)) + 17))) = true →
      (331667116107881857004015087517636447670873574697118648982286557879489695101651985317803307952383125638177628555085963403226383018811993806245904891184938415253508325235).testBit r.val = true := by decide

theorem even22_b17_s5_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (80000000 + (i : ZMod 557)) + 17))) = true) :
    (331667116107881857004015087517636447670873574697118648982286557879489695101651985317803307952383125638177628555085963403226383018811993806245904891184938415253508325235).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_557_fin r
  change even22A557
    (-(33 * (46 * (80000000 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S5Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1225694864837316577654601719129168058244790421050138058025436256538275488530124237293779859882364535132657150946224430133325478560222436963139183439355) (.leaf 503 19601978625903071957686369332989608667416603321735128969312593305032477640067567390948933313386436060497408096789045308489842138007869744154432934445055)) (.node (.leaf 509 1569180822675272775687990097345583068420810673089573124145795657558392384179986841116886124351241708958971609585791004706270610353296897023703725870413823) (.leaf 521 6435687143155293079743346895427384392279065921563614275956500155204231160230788109381032082096639931526583524820772926933676745575683881675087514681302668285))) (.node (.node (.leaf 523 26597279935541293941327324261486377073480424748290028357024653134356044408622667767297340333623742085610173500894273155687976839079078873842547338936124949951) (.leaf 541 7197050434482100320131610573067616512780153418686098100524511978027121681408594708158672281306046449328994575459483727708289943473331872296128117320551455732037565)) (.node (.leaf 547 381507882899057585189284451217128351597520980450446817894702084738802916823457023568085716493352359381576886426556267466970248458945923371542742987032177999800663895) (.leaf 557 331667116107881857004015087517636447670873574697118648982286557879489695101651985317803307952383125638177628555085963403226383018811993806245904891184938415253508325235))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S5Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S5Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
