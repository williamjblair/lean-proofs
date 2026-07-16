import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s1_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (16000000 + (r.val : ZMod 499)) + 17))) = true →
      (952607813548248099936413267773299264595268544284389210369378032805528278109293947625632368871347919243853727182156316203307294267376460272030365638142).testBit r.val = true := by decide

theorem even22_b17_s1_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (16000000 + (i : ZMod 499)) + 17))) = true) :
    (952607813548248099936413267773299264595268544284389210369378032805528278109293947625632368871347919243853727182156316203307294267376460272030365638142).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_499_fin r
  change even22A499
    (-(33 * (46 * (16000000 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (16000000 + (r.val : ZMod 503)) + 17))) = true →
      (13041934953845088135476573362564664692760919043673258382494566228985051572412682299530914603381369978036914779015665354271671130440416052884017149106143).testBit r.val = true := by decide

theorem even22_b17_s1_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (16000000 + (i : ZMod 503)) + 17))) = true) :
    (13041934953845088135476573362564664692760919043673258382494566228985051572412682299530914603381369978036914779015665354271671130440416052884017149106143).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_503_fin r
  change even22A503
    (-(33 * (46 * (16000000 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (16000000 + (r.val : ZMod 509)) + 17))) = true →
      (1668553157535875800629878894801131313690319706262535081336717965302014025324027674160506109517206915335756864310022259595287202307305274114720713041491961).testBit r.val = true := by decide

theorem even22_b17_s1_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (16000000 + (i : ZMod 509)) + 17))) = true) :
    (1668553157535875800629878894801131313690319706262535081336717965302014025324027674160506109517206915335756864310022259595287202307305274114720713041491961).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_509_fin r
  change even22A509
    (-(33 * (46 * (16000000 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (16000000 + (r.val : ZMod 521)) + 17))) = true →
      (4022340527910561326499465637699213567226438487844277888642744574404161597467943989892543751638285358769245074972514157710194064875948386159736442544577281919).testBit r.val = true := by decide

theorem even22_b17_s1_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (16000000 + (i : ZMod 521)) + 17))) = true) :
    (4022340527910561326499465637699213567226438487844277888642744574404161597467943989892543751638285358769245074972514157710194064875948386159736442544577281919).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_521_fin r
  change even22A521
    (-(33 * (46 * (16000000 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (16000000 + (r.val : ZMod 523)) + 17))) = true →
      (26601043264155045545882423275820323087153216478709081090250560431004811690150667668820364705270705021396741690040960215025572879420608091040800820991725862911).testBit r.val = true := by decide

theorem even22_b17_s1_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (16000000 + (i : ZMod 523)) + 17))) = true) :
    (26601043264155045545882423275820323087153216478709081090250560431004811690150667668820364705270705021396741690040960215025572879420608091040800820991725862911).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_523_fin r
  change even22A523
    (-(33 * (46 * (16000000 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (16000000 + (r.val : ZMod 541)) + 17))) = true →
      (5173750414471012804345329696776226250153414236788936876174287393340776919523742263684112907656378648036414976802582349650153106795363393185645898556944070461028319).testBit r.val = true := by decide

theorem even22_b17_s1_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (16000000 + (i : ZMod 541)) + 17))) = true) :
    (5173750414471012804345329696776226250153414236788936876174287393340776919523742263684112907656378648036414976802582349650153106795363393185645898556944070461028319).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_541_fin r
  change even22A541
    (-(33 * (46 * (16000000 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (16000000 + (r.val : ZMod 547)) + 17))) = true →
      (460674685996382100368192764228808981173563191635759392322321908974821881541779605523894450863428883479922745084063786963428993903250593035566197420328506539156406271).testBit r.val = true := by decide

theorem even22_b17_s1_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (16000000 + (i : ZMod 547)) + 17))) = true) :
    (460674685996382100368192764228808981173563191635759392322321908974821881541779605523894450863428883479922745084063786963428993903250593035566197420328506539156406271).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_547_fin r
  change even22A547
    (-(33 * (46 * (16000000 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (16000000 + (r.val : ZMod 557)) + 17))) = true →
      (454006086010806737628821297309243811177015818102092238372493261909457442955883495307590436080494521005005568692304027903029965434456563480300820456608671297064855919359).testBit r.val = true := by decide

theorem even22_b17_s1_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (16000000 + (i : ZMod 557)) + 17))) = true) :
    (454006086010806737628821297309243811177015818102092238372493261909457442955883495307590436080494521005005568692304027903029965434456563480300820456608671297064855919359).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_557_fin r
  change even22A557
    (-(33 * (46 * (16000000 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S1Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 952607813548248099936413267773299264595268544284389210369378032805528278109293947625632368871347919243853727182156316203307294267376460272030365638142) (.leaf 503 13041934953845088135476573362564664692760919043673258382494566228985051572412682299530914603381369978036914779015665354271671130440416052884017149106143)) (.node (.leaf 509 1668553157535875800629878894801131313690319706262535081336717965302014025324027674160506109517206915335756864310022259595287202307305274114720713041491961) (.leaf 521 4022340527910561326499465637699213567226438487844277888642744574404161597467943989892543751638285358769245074972514157710194064875948386159736442544577281919))) (.node (.node (.leaf 523 26601043264155045545882423275820323087153216478709081090250560431004811690150667668820364705270705021396741690040960215025572879420608091040800820991725862911) (.leaf 541 5173750414471012804345329696776226250153414236788936876174287393340776919523742263684112907656378648036414976802582349650153106795363393185645898556944070461028319)) (.node (.leaf 547 460674685996382100368192764228808981173563191635759392322321908974821881541779605523894450863428883479922745084063786963428993903250593035566197420328506539156406271) (.leaf 557 454006086010806737628821297309243811177015818102092238372493261909457442955883495307590436080494521005005568692304027903029965434456563480300820456608671297064855919359))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S1Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S1Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
