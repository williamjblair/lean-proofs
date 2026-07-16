import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s2_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (32000000 + (r.val : ZMod 499)) + 17))) = true →
      (1568141705782747202367072441352062088098640135054603701912232966975970711432274154566386127791934686854910355523222720982677036570362158299532056591835).testBit r.val = true := by decide

theorem even22_b17_s2_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (32000000 + (i : ZMod 499)) + 17))) = true) :
    (1568141705782747202367072441352062088098640135054603701912232966975970711432274154566386127791934686854910355523222720982677036570362158299532056591835).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_499_fin r
  change even22A499
    (-(33 * (46 * (32000000 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (32000000 + (r.val : ZMod 503)) + 17))) = true →
      (26185913377605886400313436211691916540812058713591355402276478372697082019822798355430739379123965633428201822000424099522446207915454816248589872103421).testBit r.val = true := by decide

theorem even22_b17_s2_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (32000000 + (i : ZMod 503)) + 17))) = true) :
    (26185913377605886400313436211691916540812058713591355402276478372697082019822798355430739379123965633428201822000424099522446207915454816248589872103421).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_503_fin r
  change even22A503
    (-(33 * (46 * (32000000 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (32000000 + (r.val : ZMod 509)) + 17))) = true →
      (1597357075703732609693757593685146710271641577435641889262896503305520156839401768985278421572656002652318197992293173478011007801633825947424474462680523).testBit r.val = true := by decide

theorem even22_b17_s2_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (32000000 + (i : ZMod 509)) + 17))) = true) :
    (1597357075703732609693757593685146710271641577435641889262896503305520156839401768985278421572656002652318197992293173478011007801633825947424474462680523).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_509_fin r
  change even22A509
    (-(33 * (46 * (32000000 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (32000000 + (r.val : ZMod 521)) + 17))) = true →
      (6864782827579415767885950278916995549246782222617710271897554825262198756572554518917076279758075248864041860092447933427625520938345581782125755810718922751).testBit r.val = true := by decide

theorem even22_b17_s2_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (32000000 + (i : ZMod 521)) + 17))) = true) :
    (6864782827579415767885950278916995549246782222617710271897554825262198756572554518917076279758075248864041860092447933427625520938345581782125755810718922751).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_521_fin r
  change even22A521
    (-(33 * (46 * (32000000 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (32000000 + (r.val : ZMod 523)) + 17))) = true →
      (20593437929422475233438951009856386466716593648175884487106147604255855649390498153716011769859369350371818797996994472237591245544040865029243540090998751215).testBit r.val = true := by decide

theorem even22_b17_s2_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (32000000 + (i : ZMod 523)) + 17))) = true) :
    (20593437929422475233438951009856386466716593648175884487106147604255855649390498153716011769859369350371818797996994472237591245544040865029243540090998751215).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_523_fin r
  change even22A523
    (-(33 * (46 * (32000000 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (32000000 + (r.val : ZMod 541)) + 17))) = true →
      (4688248305766009976559499839571051239406988756255636930689696897593384828998656153653719153330935819746189674106550332475135334572061809486431775594156755634321531).testBit r.val = true := by decide

theorem even22_b17_s2_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (32000000 + (i : ZMod 541)) + 17))) = true) :
    (4688248305766009976559499839571051239406988756255636930689696897593384828998656153653719153330935819746189674106550332475135334572061809486431775594156755634321531).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_541_fin r
  change even22A541
    (-(33 * (46 * (32000000 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (32000000 + (r.val : ZMod 547)) + 17))) = true →
      (460644604452240039662831722700053259094166919715277939871160926323614089065076789969767839183564479851765338119373743293325607225831287532492304342353040084807090173).testBit r.val = true := by decide

theorem even22_b17_s2_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (32000000 + (i : ZMod 547)) + 17))) = true) :
    (460644604452240039662831722700053259094166919715277939871160926323614089065076789969767839183564479851765338119373743293325607225831287532492304342353040084807090173).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_547_fin r
  change even22A547
    (-(33 * (46 * (32000000 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (32000000 + (r.val : ZMod 557)) + 17))) = true →
      (331551935592894147495170773127403644432003141313410418378788545799093854055092916398571139762626636825445094368207603898874642613760882291890604106092307745470556927979).testBit r.val = true := by decide

theorem even22_b17_s2_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (32000000 + (i : ZMod 557)) + 17))) = true) :
    (331551935592894147495170773127403644432003141313410418378788545799093854055092916398571139762626636825445094368207603898874642613760882291890604106092307745470556927979).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_557_fin r
  change even22A557
    (-(33 * (46 * (32000000 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S2Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1568141705782747202367072441352062088098640135054603701912232966975970711432274154566386127791934686854910355523222720982677036570362158299532056591835) (.leaf 503 26185913377605886400313436211691916540812058713591355402276478372697082019822798355430739379123965633428201822000424099522446207915454816248589872103421)) (.node (.leaf 509 1597357075703732609693757593685146710271641577435641889262896503305520156839401768985278421572656002652318197992293173478011007801633825947424474462680523) (.leaf 521 6864782827579415767885950278916995549246782222617710271897554825262198756572554518917076279758075248864041860092447933427625520938345581782125755810718922751))) (.node (.node (.leaf 523 20593437929422475233438951009856386466716593648175884487106147604255855649390498153716011769859369350371818797996994472237591245544040865029243540090998751215) (.leaf 541 4688248305766009976559499839571051239406988756255636930689696897593384828998656153653719153330935819746189674106550332475135334572061809486431775594156755634321531)) (.node (.leaf 547 460644604452240039662831722700053259094166919715277939871160926323614089065076789969767839183564479851765338119373743293325607225831287532492304342353040084807090173) (.leaf 557 331551935592894147495170773127403644432003141313410418378788545799093854055092916398571139762626636825445094368207603898874642613760882291890604106092307745470556927979))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S2Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S2Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
