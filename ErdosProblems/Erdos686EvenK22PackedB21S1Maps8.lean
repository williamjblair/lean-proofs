import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (16000000 + (r.val : ZMod 499)) + 21))) = true →
      (1406428832475392974281040238244849246937096783967576856421606241253222105565788666121585969113205222060522410115179528883792929800565471599339224694710).testBit r.val = true := by decide

theorem even22_b21_s1_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (16000000 + (i : ZMod 499)) + 21))) = true) :
    (1406428832475392974281040238244849246937096783967576856421606241253222105565788666121585969113205222060522410115179528883792929800565471599339224694710).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_499_fin r
  change even22A499
    (-(33 * (46 * (16000000 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (16000000 + (r.val : ZMod 503)) + 21))) = true →
      (19333461716887273219504448570442857576023882615784373770856004893799746530091759474969545629435814783792525823057928312375665858039811600449481625025455).testBit r.val = true := by decide

theorem even22_b21_s1_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (16000000 + (i : ZMod 503)) + 21))) = true) :
    (19333461716887273219504448570442857576023882615784373770856004893799746530091759474969545629435814783792525823057928312375665858039811600449481625025455).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_503_fin r
  change even22A503
    (-(33 * (46 * (16000000 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (16000000 + (r.val : ZMod 509)) + 21))) = true →
      (1675859312668402903618226908067963213446027070378940380000774439533067954094498324592197077781516053465568362893999334133478295481713151657274083257286622).testBit r.val = true := by decide

theorem even22_b21_s1_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (16000000 + (i : ZMod 509)) + 21))) = true) :
    (1675859312668402903618226908067963213446027070378940380000774439533067954094498324592197077781516053465568362893999334133478295481713151657274083257286622).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_509_fin r
  change even22A509
    (-(33 * (46 * (16000000 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (16000000 + (r.val : ZMod 521)) + 21))) = true →
      (6857242570516001757598682164000158889773738469597501552868862966127798833564670406400278380200438410810430177852132904899204063379383945427074071280328114175).testBit r.val = true := by decide

theorem even22_b21_s1_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (16000000 + (i : ZMod 521)) + 21))) = true) :
    (6857242570516001757598682164000158889773738469597501552868862966127798833564670406400278380200438410810430177852132904899204063379383945427074071280328114175).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_521_fin r
  change even22A521
    (-(33 * (46 * (16000000 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (16000000 + (r.val : ZMod 523)) + 21))) = true →
      (25635519033092740504452089673171564957748430023709173942969166913695736694423113150648957672442352875034767178338472263089036431964296926493775913354738401279).testBit r.val = true := by decide

theorem even22_b21_s1_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (16000000 + (i : ZMod 523)) + 21))) = true) :
    (25635519033092740504452089673171564957748430023709173942969166913695736694423113150648957672442352875034767178338472263089036431964296926493775913354738401279).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_523_fin r
  change even22A523
    (-(33 * (46 * (16000000 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (16000000 + (r.val : ZMod 541)) + 21))) = true →
      (1778257185408449123717137775751649034561061266618789575798437817859351018696562252590527336701477516702491529652620368671716165720348333162476613213095426602644958).testBit r.val = true := by decide

theorem even22_b21_s1_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (16000000 + (i : ZMod 541)) + 21))) = true) :
    (1778257185408449123717137775751649034561061266618789575798437817859351018696562252590527336701477516702491529652620368671716165720348333162476613213095426602644958).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_541_fin r
  change even22A541
    (-(33 * (46 * (16000000 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (16000000 + (r.val : ZMod 547)) + 21))) = true →
      (230231693762216199335635222341782811072818227037320615458465557635909799726643767587028942151667765591093508801408190958979632629567154163747707387352820521490448247).testBit r.val = true := by decide

theorem even22_b21_s1_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (16000000 + (i : ZMod 547)) + 21))) = true) :
    (230231693762216199335635222341782811072818227037320615458465557635909799726643767587028942151667765591093508801408190958979632629567154163747707387352820521490448247).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_547_fin r
  change even22A547
    (-(33 * (46 * (16000000 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (16000000 + (r.val : ZMod 557)) + 21))) = true →
      (471739884855161123618732402563328719117880354174126806610920830461426140950352560072795055728228775502755657584807937685722531315177126475988138868672978121373001428991).testBit r.val = true := by decide

theorem even22_b21_s1_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (16000000 + (i : ZMod 557)) + 21))) = true) :
    (471739884855161123618732402563328719117880354174126806610920830461426140950352560072795055728228775502755657584807937685722531315177126475988138868672978121373001428991).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_557_fin r
  change even22A557
    (-(33 * (46 * (16000000 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1406428832475392974281040238244849246937096783967576856421606241253222105565788666121585969113205222060522410115179528883792929800565471599339224694710) (.leaf 503 19333461716887273219504448570442857576023882615784373770856004893799746530091759474969545629435814783792525823057928312375665858039811600449481625025455)) (.node (.leaf 509 1675859312668402903618226908067963213446027070378940380000774439533067954094498324592197077781516053465568362893999334133478295481713151657274083257286622) (.leaf 521 6857242570516001757598682164000158889773738469597501552868862966127798833564670406400278380200438410810430177852132904899204063379383945427074071280328114175))) (.node (.node (.leaf 523 25635519033092740504452089673171564957748430023709173942969166913695736694423113150648957672442352875034767178338472263089036431964296926493775913354738401279) (.leaf 541 1778257185408449123717137775751649034561061266618789575798437817859351018696562252590527336701477516702491529652620368671716165720348333162476613213095426602644958)) (.node (.leaf 547 230231693762216199335635222341782811072818227037320615458465557635909799726643767587028942151667765591093508801408190958979632629567154163747707387352820521490448247) (.leaf 557 471739884855161123618732402563328719117880354174126806610920830461426140950352560072795055728228775502755657584807937685722531315177126475988138868672978121373001428991))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
