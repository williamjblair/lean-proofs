import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s4_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (64000000 + (r.val : ZMod 499)) + 17))) = true →
      (1631338357424531521919763404124401084386241830860326371050596848483033478516190542046310123839812593095721949778330008464721394333415820572785676386303).testBit r.val = true := by decide

theorem even22_b17_s4_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (64000000 + (i : ZMod 499)) + 17))) = true) :
    (1631338357424531521919763404124401084386241830860326371050596848483033478516190542046310123839812593095721949778330008464721394333415820572785676386303).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_499_fin r
  change even22A499
    (-(33 * (46 * (64000000 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (64000000 + (r.val : ZMod 503)) + 17))) = true →
      (26186999993225261612927159520839939310970421322165735484103522730814603705455181561796619364211312538262481984425626651247155221253216357348732850667199).testBit r.val = true := by decide

theorem even22_b17_s4_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (64000000 + (i : ZMod 503)) + 17))) = true) :
    (26186999993225261612927159520839939310970421322165735484103522730814603705455181561796619364211312538262481984425626651247155221253216357348732850667199).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_503_fin r
  change even22A503
    (-(33 * (46 * (64000000 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (64000000 + (r.val : ZMod 509)) + 17))) = true →
      (1656321249284770889227372219462396401762819992924454432133505678307902465394816605798955099659935062925683562727569862268275506535412170790543945651973595).testBit r.val = true := by decide

theorem even22_b17_s4_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (64000000 + (i : ZMod 509)) + 17))) = true) :
    (1656321249284770889227372219462396401762819992924454432133505678307902465394816605798955099659935062925683562727569862268275506535412170790543945651973595).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_509_fin r
  change even22A509
    (-(33 * (46 * (64000000 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (64000000 + (r.val : ZMod 521)) + 17))) = true →
      (6835438619634147909426792362531419188338191509532254310837612421496636880866724302525541045153203497169010330953711648889743085141206682723831654491608775163).testBit r.val = true := by decide

theorem even22_b17_s4_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (64000000 + (i : ZMod 521)) + 17))) = true) :
    (6835438619634147909426792362531419188338191509532254310837612421496636880866724302525541045153203497169010330953711648889743085141206682723831654491608775163).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_521_fin r
  change even22A521
    (-(33 * (46 * (64000000 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (64000000 + (r.val : ZMod 523)) + 17))) = true →
      (26600252535785921589316406875699709969273265134614179270698398349711410624156918339334338931521139477123382195325848741315519978000201023340850509819239399423).testBit r.val = true := by decide

theorem even22_b17_s4_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (64000000 + (i : ZMod 523)) + 17))) = true) :
    (26600252535785921589316406875699709969273265134614179270698398349711410624156918339334338931521139477123382195325848741315519978000201023340850509819239399423).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_523_fin r
  change even22A523
    (-(33 * (46 * (64000000 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (64000000 + (r.val : ZMod 541)) + 17))) = true →
      (5384088226930250704770172212538399802074762727914023182383245997551392554611527492620590961237126248951662139700987550565832251181093119978721163446396042662117117).testBit r.val = true := by decide

theorem even22_b17_s4_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (64000000 + (i : ZMod 541)) + 17))) = true) :
    (5384088226930250704770172212538399802074762727914023182383245997551392554611527492620590961237126248951662139700987550565832251181093119978721163446396042662117117).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_541_fin r
  change even22A541
    (-(33 * (46 * (64000000 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (64000000 + (r.val : ZMod 547)) + 17))) = true →
      (460463812156426742063011563635074043294011258634499213887159611317164454786496121164908423285068493633706438352382837441229224906104391310676540042968692198022840063).testBit r.val = true := by decide

theorem even22_b17_s4_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (64000000 + (i : ZMod 547)) + 17))) = true) :
    (460463812156426742063011563635074043294011258634499213887159611317164454786496121164908423285068493633706438352382837441229224906104391310676540042968692198022840063).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_547_fin r
  change even22A547
    (-(33 * (46 * (64000000 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s4_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (64000000 + (r.val : ZMod 557)) + 17))) = true →
      (471736249036964938338463639844273157455821078959872716897860649947537831341788092653327810940637161642147685566516011626234251348759396524074904237724262269381326643199).testBit r.val = true := by decide

theorem even22_b17_s4_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (64000000 + (i : ZMod 557)) + 17))) = true) :
    (471736249036964938338463639844273157455821078959872716897860649947537831341788092653327810940637161642147685566516011626234251348759396524074904237724262269381326643199).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s4_map_557_fin r
  change even22A557
    (-(33 * (46 * (64000000 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S4Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1631338357424531521919763404124401084386241830860326371050596848483033478516190542046310123839812593095721949778330008464721394333415820572785676386303) (.leaf 503 26186999993225261612927159520839939310970421322165735484103522730814603705455181561796619364211312538262481984425626651247155221253216357348732850667199)) (.node (.leaf 509 1656321249284770889227372219462396401762819992924454432133505678307902465394816605798955099659935062925683562727569862268275506535412170790543945651973595) (.leaf 521 6835438619634147909426792362531419188338191509532254310837612421496636880866724302525541045153203497169010330953711648889743085141206682723831654491608775163))) (.node (.node (.leaf 523 26600252535785921589316406875699709969273265134614179270698398349711410624156918339334338931521139477123382195325848741315519978000201023340850509819239399423) (.leaf 541 5384088226930250704770172212538399802074762727914023182383245997551392554611527492620590961237126248951662139700987550565832251181093119978721163446396042662117117)) (.node (.leaf 547 460463812156426742063011563635074043294011258634499213887159611317164454786496121164908423285068493633706438352382837441229224906104391310676540042968692198022840063) (.leaf 557 471736249036964938338463639844273157455821078959872716897860649947537831341788092653327810940637161642147685566516011626234251348759396524074904237724262269381326643199))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S4Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S4Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s4_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
