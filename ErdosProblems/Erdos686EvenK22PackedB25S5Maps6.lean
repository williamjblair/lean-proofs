import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s5_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (80000000 + (r.val : ZMod 401)) + 25))) = true →
      (5164494753665385826986428312876022010083210098407469312401142426530372179058946210768938841128372914866528757188155899895).testBit r.val = true := by decide

theorem even22_b25_s5_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (80000000 + (i : ZMod 401)) + 25))) = true) :
    (5164494753665385826986428312876022010083210098407469312401142426530372179058946210768938841128372914866528757188155899895).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_401_fin r
  change even22A401
    (-(33 * (46 * (80000000 + ((i % 401 : ℕ) : ZMod 401)) + 25))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (80000000 + (r.val : ZMod 409)) + 25))) = true →
      (1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087).testBit r.val = true := by decide

theorem even22_b25_s5_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (80000000 + (i : ZMod 409)) + 25))) = true) :
    (1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_409_fin r
  change even22A409
    (-(33 * (46 * (80000000 + ((i % 409 : ℕ) : ZMod 409)) + 25))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (80000000 + (r.val : ZMod 419)) + 25))) = true →
      (1015379354290335159025586643804790813807809520707138816438543137443534409657894163683942919178516387660379089661927815055925247).testBit r.val = true := by decide

theorem even22_b25_s5_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (80000000 + (i : ZMod 419)) + 25))) = true) :
    (1015379354290335159025586643804790813807809520707138816438543137443534409657894163683942919178516387660379089661927815055925247).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_419_fin r
  change even22A419
    (-(33 * (46 * (80000000 + ((i % 419 : ℕ) : ZMod 419)) + 25))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (80000000 + (r.val : ZMod 421)) + 25))) = true →
      (5160857491612555088962510382978178987336560234072218929883709384814235551460276271206148881977492846808681646396928722907168735).testBit r.val = true := by decide

theorem even22_b25_s5_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (80000000 + (i : ZMod 421)) + 25))) = true) :
    (5160857491612555088962510382978178987336560234072218929883709384814235551460276271206148881977492846808681646396928722907168735).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_421_fin r
  change even22A421
    (-(33 * (46 * (80000000 + ((i % 421 : ℕ) : ZMod 421)) + 25))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (80000000 + (r.val : ZMod 431)) + 25))) = true →
      (4852150717914037069949644700033678261048438292295816749327180783701708129557776314086989212444856237178826748728645858432126484191).testBit r.val = true := by decide

theorem even22_b25_s5_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (80000000 + (i : ZMod 431)) + 25))) = true) :
    (4852150717914037069949644700033678261048438292295816749327180783701708129557776314086989212444856237178826748728645858432126484191).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_431_fin r
  change even22A431
    (-(33 * (46 * (80000000 + ((i % 431 : ℕ) : ZMod 431)) + 25))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (80000000 + (r.val : ZMod 433)) + 25))) = true →
      (22094373164197094214930504682877489818132315323971674655725098601578256647043721442310578624188342364776990714430566086426534739967).testBit r.val = true := by decide

theorem even22_b25_s5_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (80000000 + (i : ZMod 433)) + 25))) = true) :
    (22094373164197094214930504682877489818132315323971674655725098601578256647043721442310578624188342364776990714430566086426534739967).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_433_fin r
  change even22A433
    (-(33 * (46 * (80000000 + ((i % 433 : ℕ) : ZMod 433)) + 25))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (80000000 + (r.val : ZMod 439)) + 25))) = true →
      (1131186955785784134975073824428407125581821742881430388869272608500561663450435026203128270250332101165038510689267377169825817165791).testBit r.val = true := by decide

theorem even22_b25_s5_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (80000000 + (i : ZMod 439)) + 25))) = true) :
    (1131186955785784134975073824428407125581821742881430388869272608500561663450435026203128270250332101165038510689267377169825817165791).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_439_fin r
  change even22A439
    (-(33 * (46 * (80000000 + ((i % 439 : ℕ) : ZMod 439)) + 25))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (80000000 + (r.val : ZMod 443)) + 25))) = true →
      (22659618577601682759246923469490014693652052880747784383314893390375730607979131747598827531558659777346647808371933577505710289190767).testBit r.val = true := by decide

theorem even22_b25_s5_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (80000000 + (i : ZMod 443)) + 25))) = true) :
    (22659618577601682759246923469490014693652052880747784383314893390375730607979131747598827531558659777346647808371933577505710289190767).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_443_fin r
  change even22A443
    (-(33 * (46 * (80000000 + ((i % 443 : ℕ) : ZMod 443)) + 25))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB25S5Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5164494753665385826986428312876022010083210098407469312401142426530372179058946210768938841128372914866528757188155899895) (.leaf 409 1320815136289823345270350301419479952913905982515079749491158597670661577079705154533816044939443027213386717221971109593087)) (.node (.leaf 419 1015379354290335159025586643804790813807809520707138816438543137443534409657894163683942919178516387660379089661927815055925247) (.leaf 421 5160857491612555088962510382978178987336560234072218929883709384814235551460276271206148881977492846808681646396928722907168735))) (.node (.node (.leaf 431 4852150717914037069949644700033678261048438292295816749327180783701708129557776314086989212444856237178826748728645858432126484191) (.leaf 433 22094373164197094214930504682877489818132315323971674655725098601578256647043721442310578624188342364776990714430566086426534739967)) (.node (.leaf 439 1131186955785784134975073824428407125581821742881430388869272608500561663450435026203128270250332101165038510689267377169825817165791) (.leaf 443 22659618577601682759246923469490014693652052880747784383314893390375730607979131747598827531558659777346647808371933577505710289190767))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S5Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S5Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
