import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s4_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (64000000 + (r.val : ZMod 499)) + 29))) = true →
      (1074081292593701059464926748531195812328864262188984103988441526251958632065002471238518766318975039649056449202130387608023841047240896069585869926388).testBit r.val = true := by decide

theorem even22_b29_s4_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (64000000 + (i : ZMod 499)) + 29))) = true) :
    (1074081292593701059464926748531195812328864262188984103988441526251958632065002471238518766318975039649056449202130387608023841047240896069585869926388).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_499_fin r
  change even22A499
    (-(33 * (46 * (64000000 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (64000000 + (r.val : ZMod 503)) + 29))) = true →
      (26186725278878353479647497275666713620675526859076146032058530071308324156348163668065503979993760905526806592116853395359768671566284968930780644638617).testBit r.val = true := by decide

theorem even22_b29_s4_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (64000000 + (i : ZMod 503)) + 29))) = true) :
    (26186725278878353479647497275666713620675526859076146032058530071308324156348163668065503979993760905526806592116853395359768671566284968930780644638617).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_503_fin r
  change even22A503
    (-(33 * (46 * (64000000 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (64000000 + (r.val : ZMod 509)) + 29))) = true →
      (1451671564970913556342809967506791649183521393314350725757568754266633836979375063808864592512545311269393612946005347183478057793832848701098371380535023).testBit r.val = true := by decide

theorem even22_b29_s4_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (64000000 + (i : ZMod 509)) + 29))) = true) :
    (1451671564970913556342809967506791649183521393314350725757568754266633836979375063808864592512545311269393612946005347183478057793832848701098371380535023).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_509_fin r
  change even22A509
    (-(33 * (46 * (64000000 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (64000000 + (r.val : ZMod 521)) + 29))) = true →
      (3432398826462757395691349138774364420393556544106596025065113253869269881882682208788308799498064475261559147905111261772718471417840127549035663027490258875).testBit r.val = true := by decide

theorem even22_b29_s4_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (64000000 + (i : ZMod 521)) + 29))) = true) :
    (3432398826462757395691349138774364420393556544106596025065113253869269881882682208788308799498064475261559147905111261772718471417840127549035663027490258875).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_521_fin r
  change even22A521
    (-(33 * (46 * (64000000 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (64000000 + (r.val : ZMod 523)) + 29))) = true →
      (23812266781184651215108709231622370947355228930488709515408418243469011968499654770905916369809284559819429593840274513172597429739948857727816839764691582911).testBit r.val = true := by decide

theorem even22_b29_s4_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (64000000 + (i : ZMod 523)) + 29))) = true) :
    (23812266781184651215108709231622370947355228930488709515408418243469011968499654770905916369809284559819429593840274513172597429739948857727816839764691582911).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_523_fin r
  change even22A523
    (-(33 * (46 * (64000000 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (64000000 + (r.val : ZMod 541)) + 29))) = true →
      (3138666996158278794703227366391457435985831237617381727573985926342457541858608141526218802487942490227749695800735260236468142206151803545450200970987945581608894).testBit r.val = true := by decide

theorem even22_b29_s4_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (64000000 + (i : ZMod 541)) + 29))) = true) :
    (3138666996158278794703227366391457435985831237617381727573985926342457541858608141526218802487942490227749695800735260236468142206151803545450200970987945581608894).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_541_fin r
  change even22A541
    (-(33 * (46 * (64000000 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (64000000 + (r.val : ZMod 547)) + 29))) = true →
      (460688770841671937381875363111488117108855777175678963806799207126948673352713607340543206770296039795065447494457890154672045544114253004066021237414368158863499259).testBit r.val = true := by decide

theorem even22_b29_s4_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (64000000 + (i : ZMod 547)) + 29))) = true) :
    (460688770841671937381875363111488117108855777175678963806799207126948673352713607340543206770296039795065447494457890154672045544114253004066021237414368158863499259).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_547_fin r
  change even22A547
    (-(33 * (46 * (64000000 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (64000000 + (r.val : ZMod 557)) + 29))) = true →
      (235746414787160673610258116007654560880300397277204088808308371919564557871053454615832329464718282017033682843259253583665327619518836960806713920931160483606241834621).testBit r.val = true := by decide

theorem even22_b29_s4_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (64000000 + (i : ZMod 557)) + 29))) = true) :
    (235746414787160673610258116007654560880300397277204088808308371919564557871053454615832329464718282017033682843259253583665327619518836960806713920931160483606241834621).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_557_fin r
  change even22A557
    (-(33 * (46 * (64000000 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S4Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1074081292593701059464926748531195812328864262188984103988441526251958632065002471238518766318975039649056449202130387608023841047240896069585869926388) (.leaf 503 26186725278878353479647497275666713620675526859076146032058530071308324156348163668065503979993760905526806592116853395359768671566284968930780644638617)) (.node (.leaf 509 1451671564970913556342809967506791649183521393314350725757568754266633836979375063808864592512545311269393612946005347183478057793832848701098371380535023) (.leaf 521 3432398826462757395691349138774364420393556544106596025065113253869269881882682208788308799498064475261559147905111261772718471417840127549035663027490258875))) (.node (.node (.leaf 523 23812266781184651215108709231622370947355228930488709515408418243469011968499654770905916369809284559819429593840274513172597429739948857727816839764691582911) (.leaf 541 3138666996158278794703227366391457435985831237617381727573985926342457541858608141526218802487942490227749695800735260236468142206151803545450200970987945581608894)) (.node (.leaf 547 460688770841671937381875363111488117108855777175678963806799207126948673352713607340543206770296039795065447494457890154672045544114253004066021237414368158863499259) (.leaf 557 235746414787160673610258116007654560880300397277204088808308371919564557871053454615832329464718282017033682843259253583665327619518836960806713920931160483606241834621))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S4Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S4Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
