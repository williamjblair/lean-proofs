import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s4_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (64000000 + (r.val : ZMod 499)) + 25))) = true →
      (1362480911286776004448505220166849624069597471153817623423994815759682151122084785940639372678882511693311395901550777416882261462620543618135434983279).testBit r.val = true := by decide

theorem even22_b25_s4_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (64000000 + (i : ZMod 499)) + 25))) = true) :
    (1362480911286776004448505220166849624069597471153817623423994815759682151122084785940639372678882511693311395901550777416882261462620543618135434983279).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_499_fin r
  change even22A499
    (-(33 * (46 * (64000000 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (64000000 + (r.val : ZMod 503)) + 25))) = true →
      (25981726050903786593031471999373143976497724768620540147882804751283543568157556014254180540105518262629926082333780469098963107252332891050331678441382).testBit r.val = true := by decide

theorem even22_b25_s4_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (64000000 + (i : ZMod 503)) + 25))) = true) :
    (25981726050903786593031471999373143976497724768620540147882804751283543568157556014254180540105518262629926082333780469098963107252332891050331678441382).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_503_fin r
  change even22A503
    (-(33 * (46 * (64000000 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (64000000 + (r.val : ZMod 509)) + 25))) = true →
      (1558132126493516994200205429729738297291611091224654218078491682060078372908553914293112915345920004041150072987133631007315806982605794638817548210954143).testBit r.val = true := by decide

theorem even22_b25_s4_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (64000000 + (i : ZMod 509)) + 25))) = true) :
    (1558132126493516994200205429729738297291611091224654218078491682060078372908553914293112915345920004041150072987133631007315806982605794638817548210954143).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_509_fin r
  change even22A509
    (-(33 * (46 * (64000000 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (64000000 + (r.val : ZMod 521)) + 25))) = true →
      (6757114847304076990013737742172908332313578315704253555368164449065030979254782658490297433651620154700287612207649369774616698995790460835319118741282585562).testBit r.val = true := by decide

theorem even22_b25_s4_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (64000000 + (i : ZMod 521)) + 25))) = true) :
    (6757114847304076990013737742172908332313578315704253555368164449065030979254782658490297433651620154700287612207649369774616698995790460835319118741282585562).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_521_fin r
  change even22A521
    (-(33 * (46 * (64000000 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (64000000 + (r.val : ZMod 523)) + 25))) = true →
      (12921355846538469451047225915334848573077606365339629884501477294978871801911917963258655871956291370383991736443555878431711111385666456667583444150812376942).testBit r.val = true := by decide

theorem even22_b25_s4_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (64000000 + (i : ZMod 523)) + 25))) = true) :
    (12921355846538469451047225915334848573077606365339629884501477294978871801911917963258655871956291370383991736443555878431711111385666456667583444150812376942).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_523_fin r
  change even22A523
    (-(33 * (46 * (64000000 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (64000000 + (r.val : ZMod 541)) + 25))) = true →
      (3233585654727837932918332993575379653695755430366751640829335925367093713412933894566705360513843667540998872223254708927987849648545605932394162342482361626385895).testBit r.val = true := by decide

theorem even22_b25_s4_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (64000000 + (i : ZMod 541)) + 25))) = true) :
    (3233585654727837932918332993575379653695755430366751640829335925367093713412933894566705360513843667540998872223254708927987849648545605932394162342482361626385895).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_541_fin r
  change even22A541
    (-(33 * (46 * (64000000 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (64000000 + (r.val : ZMod 547)) + 25))) = true →
      (460660599431626082390217638089685040506500081261917485406335265318444736641594825887917379153969015571829668247689555559496515958350296707260877104470974388707360063).testBit r.val = true := by decide

theorem even22_b25_s4_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (64000000 + (i : ZMod 547)) + 25))) = true) :
    (460660599431626082390217638089685040506500081261917485406335265318444736641594825887917379153969015571829668247689555559496515958350296707260877104470974388707360063).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_547_fin r
  change even22A547
    (-(33 * (46 * (64000000 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (64000000 + (r.val : ZMod 557)) + 25))) = true →
      (471629425263237599355535726491991819004606074600493000495688096962055242593570081681429548877226949292764378659178445628435206818345240342213475444302453679294478546814).testBit r.val = true := by decide

theorem even22_b25_s4_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (64000000 + (i : ZMod 557)) + 25))) = true) :
    (471629425263237599355535726491991819004606074600493000495688096962055242593570081681429548877226949292764378659178445628435206818345240342213475444302453679294478546814).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_557_fin r
  change even22A557
    (-(33 * (46 * (64000000 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S4Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1362480911286776004448505220166849624069597471153817623423994815759682151122084785940639372678882511693311395901550777416882261462620543618135434983279) (.leaf 503 25981726050903786593031471999373143976497724768620540147882804751283543568157556014254180540105518262629926082333780469098963107252332891050331678441382)) (.node (.leaf 509 1558132126493516994200205429729738297291611091224654218078491682060078372908553914293112915345920004041150072987133631007315806982605794638817548210954143) (.leaf 521 6757114847304076990013737742172908332313578315704253555368164449065030979254782658490297433651620154700287612207649369774616698995790460835319118741282585562))) (.node (.node (.leaf 523 12921355846538469451047225915334848573077606365339629884501477294978871801911917963258655871956291370383991736443555878431711111385666456667583444150812376942) (.leaf 541 3233585654727837932918332993575379653695755430366751640829335925367093713412933894566705360513843667540998872223254708927987849648545605932394162342482361626385895)) (.node (.leaf 547 460660599431626082390217638089685040506500081261917485406335265318444736641594825887917379153969015571829668247689555559496515958350296707260877104470974388707360063) (.leaf 557 471629425263237599355535726491991819004606074600493000495688096962055242593570081681429548877226949292764378659178445628435206818345240342213475444302453679294478546814))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S4Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S4Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
