import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (32000000 + (r.val : ZMod 353)) + 25))) = true →
      (18311978031986700569496047828169602269733515741690190248959481005654081927334787338167389675117787450703599).testBit r.val = true := by decide

theorem even22_b25_s2_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (32000000 + (i : ZMod 353)) + 25))) = true) :
    (18311978031986700569496047828169602269733515741690190248959481005654081927334787338167389675117787450703599).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_353_fin r
  change even22A353
    (-(33 * (46 * (32000000 + ((i % 353 : ℕ) : ZMod 353)) + 25))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (32000000 + (r.val : ZMod 359)) + 25))) = true →
      (1174270171480369728388357464175775818913188114876247771846893506708846190325634693540709916752392745863870461).testBit r.val = true := by decide

theorem even22_b25_s2_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (32000000 + (i : ZMod 359)) + 25))) = true) :
    (1174270171480369728388357464175775818913188114876247771846893506708846190325634693540709916752392745863870461).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_359_fin r
  change even22A359
    (-(33 * (46 * (32000000 + ((i % 359 : ℕ) : ZMod 359)) + 25))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (32000000 + (r.val : ZMod 367)) + 25))) = true →
      (291219252818299041544787342965114320883189834947387833047919456978825590115082228565285207798546602961807605757).testBit r.val = true := by decide

theorem even22_b25_s2_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (32000000 + (i : ZMod 367)) + 25))) = true) :
    (291219252818299041544787342965114320883189834947387833047919456978825590115082228565285207798546602961807605757).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_367_fin r
  change even22A367
    (-(33 * (46 * (32000000 + ((i % 367 : ℕ) : ZMod 367)) + 25))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (32000000 + (r.val : ZMod 373)) + 25))) = true →
      (19234563680939509247093293229474887605771042390021341680325160198808919448301520871975698451839175683261611310523).testBit r.val = true := by decide

theorem even22_b25_s2_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (32000000 + (i : ZMod 373)) + 25))) = true) :
    (19234563680939509247093293229474887605771042390021341680325160198808919448301520871975698451839175683261611310523).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_373_fin r
  change even22A373
    (-(33 * (46 * (32000000 + ((i % 373 : ℕ) : ZMod 373)) + 25))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (32000000 + (r.val : ZMod 379)) + 25))) = true →
      (846527476732174617262403426896385287331882408988060117255432461845026042593947423156859800429081809357480461856623).testBit r.val = true := by decide

theorem even22_b25_s2_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (32000000 + (i : ZMod 379)) + 25))) = true) :
    (846527476732174617262403426896385287331882408988060117255432461845026042593947423156859800429081809357480461856623).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_379_fin r
  change even22A379
    (-(33 * (46 * (32000000 + ((i % 379 : ℕ) : ZMod 379)) + 25))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (32000000 + (r.val : ZMod 383)) + 25))) = true →
      (16928139891540312373161796762640306025548417954117445390320520844622064556628656948409672936313670213708384617480191).testBit r.val = true := by decide

theorem even22_b25_s2_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (32000000 + (i : ZMod 383)) + 25))) = true) :
    (16928139891540312373161796762640306025548417954117445390320520844622064556628656948409672936313670213708384617480191).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_383_fin r
  change even22A383
    (-(33 * (46 * (32000000 + ((i % 383 : ℕ) : ZMod 383)) + 25))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (32000000 + (r.val : ZMod 389)) + 25))) = true →
      (1260864197770878503064071987499355594001570605694715283454183537376762920090187253393341814544529546266779603838107135).testBit r.val = true := by decide

theorem even22_b25_s2_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (32000000 + (i : ZMod 389)) + 25))) = true) :
    (1260864197770878503064071987499355594001570605694715283454183537376762920090187253393341814544529546266779603838107135).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_389_fin r
  change even22A389
    (-(33 * (46 * (32000000 + ((i % 389 : ℕ) : ZMod 389)) + 25))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (32000000 + (r.val : ZMod 397)) + 25))) = true →
      (322778772135421255010888842693320727125722268416639437335702304410140141030143694338398640009620946611957548273023053775).testBit r.val = true := by decide

theorem even22_b25_s2_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (32000000 + (i : ZMod 397)) + 25))) = true) :
    (322778772135421255010888842693320727125722268416639437335702304410140141030143694338398640009620946611957548273023053775).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_397_fin r
  change even22A397
    (-(33 * (46 * (32000000 + ((i % 397 : ℕ) : ZMod 397)) + 25))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18311978031986700569496047828169602269733515741690190248959481005654081927334787338167389675117787450703599) (.leaf 359 1174270171480369728388357464175775818913188114876247771846893506708846190325634693540709916752392745863870461)) (.node (.leaf 367 291219252818299041544787342965114320883189834947387833047919456978825590115082228565285207798546602961807605757) (.leaf 373 19234563680939509247093293229474887605771042390021341680325160198808919448301520871975698451839175683261611310523))) (.node (.node (.leaf 379 846527476732174617262403426896385287331882408988060117255432461845026042593947423156859800429081809357480461856623) (.leaf 383 16928139891540312373161796762640306025548417954117445390320520844622064556628656948409672936313670213708384617480191)) (.node (.leaf 389 1260864197770878503064071987499355594001570605694715283454183537376762920090187253393341814544529546266779603838107135) (.leaf 397 322778772135421255010888842693320727125722268416639437335702304410140141030143694338398640009620946611957548273023053775))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
