import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s4_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (64000000 + (r.val : ZMod 499)) + 21))) = true →
      (1261878613291372236817591426473216123309632873653010002827737160380594061072929542018021905450920319579902146225973414401269807370271018130727545864190).testBit r.val = true := by decide

theorem even22_b21_s4_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (64000000 + (i : ZMod 499)) + 21))) = true) :
    (1261878613291372236817591426473216123309632873653010002827737160380594061072929542018021905450920319579902146225973414401269807370271018130727545864190).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_499_fin r
  change even22A499
    (-(33 * (46 * (64000000 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (64000000 + (r.val : ZMod 503)) + 21))) = true →
      (26032054711073319306719103119724578571835196559939665376365201719554561390168841733732226724748977413508962142453252593508381962558657137637719598431999).testBit r.val = true := by decide

theorem even22_b21_s4_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (64000000 + (i : ZMod 503)) + 21))) = true) :
    (26032054711073319306719103119724578571835196559939665376365201719554561390168841733732226724748977413508962142453252593508381962558657137637719598431999).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_503_fin r
  change even22A503
    (-(33 * (46 * (64000000 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (64000000 + (r.val : ZMod 509)) + 21))) = true →
      (1662850362207081152913809274146547343817237308223170677910977829497953703258395752744638653539137919312343543371299111993253713132124836530766513788845303).testBit r.val = true := by decide

theorem even22_b21_s4_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (64000000 + (i : ZMod 509)) + 21))) = true) :
    (1662850362207081152913809274146547343817237308223170677910977829497953703258395752744638653539137919312343543371299111993253713132124836530766513788845303).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_509_fin r
  change even22A509
    (-(33 * (46 * (64000000 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (64000000 + (r.val : ZMod 521)) + 21))) = true →
      (3431966699849289167934782557940245355988581861847738428901737750044211183220135951859803505900931272945874823648753670358589443493815232638018913137508474603).testBit r.val = true := by decide

theorem even22_b21_s4_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (64000000 + (i : ZMod 521)) + 21))) = true) :
    (3431966699849289167934782557940245355988581861847738428901737750044211183220135951859803505900931272945874823648753670358589443493815232638018913137508474603).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_521_fin r
  change even22A521
    (-(33 * (46 * (64000000 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (64000000 + (r.val : ZMod 523)) + 21))) = true →
      (25736286503161504876285471836740039504701353718315993036777875227323310312078072666346107989802780915462664310192604881048531977025173069708417035364525277183).testBit r.val = true := by decide

theorem even22_b21_s4_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (64000000 + (i : ZMod 523)) + 21))) = true) :
    (25736286503161504876285471836740039504701353718315993036777875227323310312078072666346107989802780915462664310192604881048531977025173069708417035364525277183).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_523_fin r
  change even22A523
    (-(33 * (46 * (64000000 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (64000000 + (r.val : ZMod 541)) + 21))) = true →
      (5398696553011564519483827700119152262900029302765480142583283799335381688070137700679237426907342389681685412173108418878110907730418106698934886340778522087260071).testBit r.val = true := by decide

theorem even22_b21_s4_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (64000000 + (i : ZMod 541)) + 21))) = true) :
    (5398696553011564519483827700119152262900029302765480142583283799335381688070137700679237426907342389681685412173108418878110907730418106698934886340778522087260071).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_541_fin r
  change even22A541
    (-(33 * (46 * (64000000 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (64000000 + (r.val : ZMod 547)) + 21))) = true →
      (460685250916449110462986105341796444438804373550471742507400458116871022880399187383820409066762318952070631289820012853310672483097666035758923901254255083329150719).testBit r.val = true := by decide

theorem even22_b21_s4_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (64000000 + (i : ZMod 547)) + 21))) = true) :
    (460685250916449110462986105341796444438804373550471742507400458116871022880399187383820409066762318952070631289820012853310672483097666035758923901254255083329150719).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_547_fin r
  change even22A547
    (-(33 * (46 * (64000000 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (64000000 + (r.val : ZMod 557)) + 21))) = true →
      (471597738661488118308182978277652306011734876602663536093096473939235920210175968759221997621260081405851305659821909590819518102063817233276303296938783235979872255821).testBit r.val = true := by decide

theorem even22_b21_s4_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (64000000 + (i : ZMod 557)) + 21))) = true) :
    (471597738661488118308182978277652306011734876602663536093096473939235920210175968759221997621260081405851305659821909590819518102063817233276303296938783235979872255821).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_557_fin r
  change even22A557
    (-(33 * (46 * (64000000 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S4Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1261878613291372236817591426473216123309632873653010002827737160380594061072929542018021905450920319579902146225973414401269807370271018130727545864190) (.leaf 503 26032054711073319306719103119724578571835196559939665376365201719554561390168841733732226724748977413508962142453252593508381962558657137637719598431999)) (.node (.leaf 509 1662850362207081152913809274146547343817237308223170677910977829497953703258395752744638653539137919312343543371299111993253713132124836530766513788845303) (.leaf 521 3431966699849289167934782557940245355988581861847738428901737750044211183220135951859803505900931272945874823648753670358589443493815232638018913137508474603))) (.node (.node (.leaf 523 25736286503161504876285471836740039504701353718315993036777875227323310312078072666346107989802780915462664310192604881048531977025173069708417035364525277183) (.leaf 541 5398696553011564519483827700119152262900029302765480142583283799335381688070137700679237426907342389681685412173108418878110907730418106698934886340778522087260071)) (.node (.leaf 547 460685250916449110462986105341796444438804373550471742507400458116871022880399187383820409066762318952070631289820012853310672483097666035758923901254255083329150719) (.leaf 557 471597738661488118308182978277652306011734876602663536093096473939235920210175968759221997621260081405851305659821909590819518102063817233276303296938783235979872255821))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S4Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S4Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
