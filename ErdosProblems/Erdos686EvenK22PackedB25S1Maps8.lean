import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s1_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (16000000 + (r.val : ZMod 499)) + 25))) = true →
      (1635895352785649538269731925574354089968279678695983961767124993092152736371940285871655881406859107074205215195985586268368124292660958331224670850687).testBit r.val = true := by decide

theorem even22_b25_s1_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (16000000 + (i : ZMod 499)) + 25))) = true) :
    (1635895352785649538269731925574354089968279678695983961767124993092152736371940285871655881406859107074205215195985586268368124292660958331224670850687).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_499_fin r
  change even22A499
    (-(33 * (46 * (16000000 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (16000000 + (r.val : ZMod 503)) + 25))) = true →
      (26187117058796270586317463816372107089626815881688490559649927764796320788996734073924581202896746141603903583267330525873626883788238068097019633729515).testBit r.val = true := by decide

theorem even22_b25_s1_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (16000000 + (i : ZMod 503)) + 25))) = true) :
    (26187117058796270586317463816372107089626815881688490559649927764796320788996734073924581202896746141603903583267330525873626883788238068097019633729515).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_503_fin r
  change even22A503
    (-(33 * (46 * (16000000 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (16000000 + (r.val : ZMod 509)) + 25))) = true →
      (1343697849667611283169459345363230859492696234832593243186444712393312150191921530456583849972509572797862506608254735931043040174560286780532022509853694).testBit r.val = true := by decide

theorem even22_b25_s1_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (16000000 + (i : ZMod 509)) + 25))) = true) :
    (1343697849667611283169459345363230859492696234832593243186444712393312150191921530456583849972509572797862506608254735931043040174560286780532022509853694).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_509_fin r
  change even22A509
    (-(33 * (46 * (16000000 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (16000000 + (r.val : ZMod 521)) + 25))) = true →
      (6857457900006494263593123689943899710036624352490542634755250699763316607764923114723304991784391790525224816282038555750277262285089153540388434841238486654).testBit r.val = true := by decide

theorem even22_b25_s1_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (16000000 + (i : ZMod 521)) + 25))) = true) :
    (6857457900006494263593123689943899710036624352490542634755250699763316607764923114723304991784391790525224816282038555750277262285089153540388434841238486654).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_521_fin r
  change even22A521
    (-(33 * (46 * (16000000 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (16000000 + (r.val : ZMod 523)) + 25))) = true →
      (14546528458083125713978536721419345428609804897622268779462335327166583292067595239603120199856889996536741682118296594294875439513644947462382493405078618075).testBit r.val = true := by decide

theorem even22_b25_s1_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (16000000 + (i : ZMod 523)) + 25))) = true) :
    (14546528458083125713978536721419345428609804897622268779462335327166583292067595239603120199856889996536741682118296594294875439513644947462382493405078618075).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_523_fin r
  change even22A523
    (-(33 * (46 * (16000000 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (16000000 + (r.val : ZMod 541)) + 25))) = true →
      (6677471048055209355688031279450284397046653510368934275140555590817242986445517982625075665474744414772314132636933405943319229413785637156872542889675915874238451).testBit r.val = true := by decide

theorem even22_b25_s1_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (16000000 + (i : ZMod 541)) + 25))) = true) :
    (6677471048055209355688031279450284397046653510368934275140555590817242986445517982625075665474744414772314132636933405943319229413785637156872542889675915874238451).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_541_fin r
  change even22A541
    (-(33 * (46 * (16000000 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (16000000 + (r.val : ZMod 547)) + 25))) = true →
      (279776198165749647781244828470748333595349930472343787401521469346679782740866031026376473307764125868789322821802619237011408486640033095915932516224758323909484543).testBit r.val = true := by decide

theorem even22_b25_s1_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (16000000 + (i : ZMod 547)) + 25))) = true) :
    (279776198165749647781244828470748333595349930472343787401521469346679782740866031026376473307764125868789322821802619237011408486640033095915932516224758323909484543).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_547_fin r
  change even22A547
    (-(33 * (46 * (16000000 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (16000000 + (r.val : ZMod 557)) + 25))) = true →
      (467714037228122887489852944229234831850305917736339936965752047640279428429465940335848115070919653089982404711214443726449613104232813848340151831298269518085204995967).testBit r.val = true := by decide

theorem even22_b25_s1_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (16000000 + (i : ZMod 557)) + 25))) = true) :
    (467714037228122887489852944229234831850305917736339936965752047640279428429465940335848115070919653089982404711214443726449613104232813848340151831298269518085204995967).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_557_fin r
  change even22A557
    (-(33 * (46 * (16000000 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S1Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1635895352785649538269731925574354089968279678695983961767124993092152736371940285871655881406859107074205215195985586268368124292660958331224670850687) (.leaf 503 26187117058796270586317463816372107089626815881688490559649927764796320788996734073924581202896746141603903583267330525873626883788238068097019633729515)) (.node (.leaf 509 1343697849667611283169459345363230859492696234832593243186444712393312150191921530456583849972509572797862506608254735931043040174560286780532022509853694) (.leaf 521 6857457900006494263593123689943899710036624352490542634755250699763316607764923114723304991784391790525224816282038555750277262285089153540388434841238486654))) (.node (.node (.leaf 523 14546528458083125713978536721419345428609804897622268779462335327166583292067595239603120199856889996536741682118296594294875439513644947462382493405078618075) (.leaf 541 6677471048055209355688031279450284397046653510368934275140555590817242986445517982625075665474744414772314132636933405943319229413785637156872542889675915874238451)) (.node (.leaf 547 279776198165749647781244828470748333595349930472343787401521469346679782740866031026376473307764125868789322821802619237011408486640033095915932516224758323909484543) (.leaf 557 467714037228122887489852944229234831850305917736339936965752047640279428429465940335848115070919653089982404711214443726449613104232813848340151831298269518085204995967))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S1Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S1Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
