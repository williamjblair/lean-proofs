import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s2_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (32000000 + (r.val : ZMod 499)) + 21))) = true →
      (268520323148425264866231687132798953082216065547246025997110381562989658016250617809629691579743759912264112300532596902005960261810224017396467481597).testBit r.val = true := by decide

theorem even22_b21_s2_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (32000000 + (i : ZMod 499)) + 21))) = true) :
    (268520323148425264866231687132798953082216065547246025997110381562989658016250617809629691579743759912264112300532596902005960261810224017396467481597).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_499_fin r
  change even22A499
    (-(33 * (46 * (32000000 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (32000000 + (r.val : ZMod 503)) + 21))) = true →
      (7977284928526022774039383904960650673830913334107126844928151411347720450587332974209127254743596734660152172321187828561726633571886659212985969262591).testBit r.val = true := by decide

theorem even22_b21_s2_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (32000000 + (i : ZMod 503)) + 21))) = true) :
    (7977284928526022774039383904960650673830913334107126844928151411347720450587332974209127254743596734660152172321187828561726633571886659212985969262591).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_503_fin r
  change even22A503
    (-(33 * (46 * (32000000 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (32000000 + (r.val : ZMod 509)) + 21))) = true →
      (1453275906260246408703285940646693799406087799236939273148521857460953626957786919209826525633932736000974224681676073183769590237643788113069367306936251).testBit r.val = true := by decide

theorem even22_b21_s2_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (32000000 + (i : ZMod 509)) + 21))) = true) :
    (1453275906260246408703285940646693799406087799236939273148521857460953626957786919209826525633932736000974224681676073183769590237643788113069367306936251).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_509_fin r
  change even22A509
    (-(33 * (46 * (32000000 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (32000000 + (r.val : ZMod 521)) + 21))) = true →
      (6757107807986744582293358291801827385004989065732405577415704873472929115961461936110197125157329088381993939521334179608941356462646805327443759236470800039).testBit r.val = true := by decide

theorem even22_b21_s2_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (32000000 + (i : ZMod 521)) + 21))) = true) :
    (6757107807986744582293358291801827385004989065732405577415704873472929115961461936110197125157329088381993939521334179608941356462646805327443759236470800039).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_521_fin r
  change even22A521
    (-(33 * (46 * (32000000 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (32000000 + (r.val : ZMod 523)) + 21))) = true →
      (27030088207927538860900928999125006251791824050950488188612922615135872824839264841492590100218683460443005231112465100884719868492810350740544898744780057599).testBit r.val = true := by decide

theorem even22_b21_s2_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (32000000 + (i : ZMod 523)) + 21))) = true) :
    (27030088207927538860900928999125006251791824050950488188612922615135872824839264841492590100218683460443005231112465100884719868492810350740544898744780057599).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_523_fin r
  change even22A523
    (-(33 * (46 * (32000000 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (32000000 + (r.val : ZMod 541)) + 21))) = true →
      (6748204943340905331518269822133677801315967943370557004301071264877229963806053213884399020926379410523820220089974526009220702510547547525844516956606445734842291).testBit r.val = true := by decide

theorem even22_b21_s2_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (32000000 + (i : ZMod 541)) + 21))) = true) :
    (6748204943340905331518269822133677801315967943370557004301071264877229963806053213884399020926379410523820220089974526009220702510547547525844516956606445734842291).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_541_fin r
  change even22A541
    (-(33 * (46 * (32000000 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (32000000 + (r.val : ZMod 547)) + 21))) = true →
      (459556135838029436161175451770183929027594392965997095291482667537372414675933722353504648015346636274789527468950809109673215951438880941121122762876084790972907103).testBit r.val = true := by decide

theorem even22_b21_s2_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (32000000 + (i : ZMod 547)) + 21))) = true) :
    (459556135838029436161175451770183929027594392965997095291482667537372414675933722353504648015346636274789527468950809109673215951438880941121122762876084790972907103).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_547_fin r
  change even22A547
    (-(33 * (46 * (32000000 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (32000000 + (r.val : ZMod 557)) + 21))) = true →
      (441699686921439301138360640081003637538602264660816103942708442821722538321702372187326151511992173223772728458203547636791084977716597077796132084323110326332923834331).testBit r.val = true := by decide

theorem even22_b21_s2_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (32000000 + (i : ZMod 557)) + 21))) = true) :
    (441699686921439301138360640081003637538602264660816103942708442821722538321702372187326151511992173223772728458203547636791084977716597077796132084323110326332923834331).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_557_fin r
  change even22A557
    (-(33 * (46 * (32000000 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S2Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 268520323148425264866231687132798953082216065547246025997110381562989658016250617809629691579743759912264112300532596902005960261810224017396467481597) (.leaf 503 7977284928526022774039383904960650673830913334107126844928151411347720450587332974209127254743596734660152172321187828561726633571886659212985969262591)) (.node (.leaf 509 1453275906260246408703285940646693799406087799236939273148521857460953626957786919209826525633932736000974224681676073183769590237643788113069367306936251) (.leaf 521 6757107807986744582293358291801827385004989065732405577415704873472929115961461936110197125157329088381993939521334179608941356462646805327443759236470800039))) (.node (.node (.leaf 523 27030088207927538860900928999125006251791824050950488188612922615135872824839264841492590100218683460443005231112465100884719868492810350740544898744780057599) (.leaf 541 6748204943340905331518269822133677801315967943370557004301071264877229963806053213884399020926379410523820220089974526009220702510547547525844516956606445734842291)) (.node (.leaf 547 459556135838029436161175451770183929027594392965997095291482667537372414675933722353504648015346636274789527468950809109673215951438880941121122762876084790972907103) (.leaf 557 441699686921439301138360640081003637538602264660816103942708442821722538321702372187326151511992173223772728458203547636791084977716597077796132084323110326332923834331))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S2Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S2Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
