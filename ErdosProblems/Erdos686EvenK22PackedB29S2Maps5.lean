import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s2_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (32000000 + (r.val : ZMod 353)) + 29))) = true →
      (17720579270040904184531545364995778528196156846292674664718949163352530371958679500947735829629997986611037).testBit r.val = true := by decide

theorem even22_b29_s2_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (32000000 + (i : ZMod 353)) + 29))) = true) :
    (17720579270040904184531545364995778528196156846292674664718949163352530371958679500947735829629997986611037).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_353_fin r
  change even22A353
    (-(33 * (46 * (32000000 + ((i % 353 : ℕ) : ZMod 353)) + 29))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (32000000 + (r.val : ZMod 359)) + 29))) = true →
      (1155922742522543236104415334465047616378844976614923822238436451374541096011422736317168986779210438412206079).testBit r.val = true := by decide

theorem even22_b29_s2_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (32000000 + (i : ZMod 359)) + 29))) = true) :
    (1155922742522543236104415334465047616378844976614923822238436451374541096011422736317168986779210438412206079).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_359_fin r
  change even22A359
    (-(33 * (46 * (32000000 + ((i % 359 : ℕ) : ZMod 359)) + 29))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (32000000 + (r.val : ZMod 367)) + 29))) = true →
      (147738006705445142990837046831832162690119124851772396198295131250818452639190574213230966134902898664200994687).testBit r.val = true := by decide

theorem even22_b29_s2_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (32000000 + (i : ZMod 367)) + 29))) = true) :
    (147738006705445142990837046831832162690119124851772396198295131250818452639190574213230966134902898664200994687).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_367_fin r
  change even22A367
    (-(33 * (46 * (32000000 + ((i % 367 : ℕ) : ZMod 367)) + 29))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (32000000 + (r.val : ZMod 373)) + 29))) = true →
      (19088954112715724453072238959086421118268919561539218377790534803856983217497533031005761905696355833543533789183).testBit r.val = true := by decide

theorem even22_b29_s2_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (32000000 + (i : ZMod 373)) + 29))) = true) :
    (19088954112715724453072238959086421118268919561539218377790534803856983217497533031005761905696355833543533789183).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_373_fin r
  change even22A373
    (-(33 * (46 * (32000000 + ((i % 373 : ℕ) : ZMod 373)) + 29))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (32000000 + (r.val : ZMod 379)) + 29))) = true →
      (1226493331721899577563127456159319746963704936684770383540124080222700251359674148465142951608304698016192840859647).testBit r.val = true := by decide

theorem even22_b29_s2_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (32000000 + (i : ZMod 379)) + 29))) = true) :
    (1226493331721899577563127456159319746963704936684770383540124080222700251359674148465142951608304698016192840859647).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_379_fin r
  change even22A379
    (-(33 * (46 * (32000000 + ((i % 379 : ℕ) : ZMod 379)) + 29))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (32000000 + (r.val : ZMod 383)) + 29))) = true →
      (15833827122205044209152781856838674213649192847608917685930913014773253935317495736157193763287450056966900693336059).testBit r.val = true := by decide

theorem even22_b29_s2_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (32000000 + (i : ZMod 383)) + 29))) = true) :
    (15833827122205044209152781856838674213649192847608917685930913014773253935317495736157193763287450056966900693336059).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_383_fin r
  change even22A383
    (-(33 * (46 * (32000000 + ((i % 383 : ℕ) : ZMod 383)) + 29))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (32000000 + (r.val : ZMod 389)) + 29))) = true →
      (625506848367758437932920111494445203933108504801001635386379351870071433249344712875404877105245699770627492352622079).testBit r.val = true := by decide

theorem even22_b29_s2_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (32000000 + (i : ZMod 389)) + 29))) = true) :
    (625506848367758437932920111494445203933108504801001635386379351870071433249344712875404877105245699770627492352622079).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_389_fin r
  change even22A389
    (-(33 * (46 * (32000000 + ((i % 389 : ℕ) : ZMod 389)) + 29))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (32000000 + (r.val : ZMod 397)) + 29))) = true →
      (281162861633567742614446579132542248592527506883170751215161368256413088388501829235055641383624596202339956195298967535).testBit r.val = true := by decide

theorem even22_b29_s2_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (32000000 + (i : ZMod 397)) + 29))) = true) :
    (281162861633567742614446579132542248592527506883170751215161368256413088388501829235055641383624596202339956195298967535).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_397_fin r
  change even22A397
    (-(33 * (46 * (32000000 + ((i % 397 : ℕ) : ZMod 397)) + 29))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB29S2Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 17720579270040904184531545364995778528196156846292674664718949163352530371958679500947735829629997986611037) (.leaf 359 1155922742522543236104415334465047616378844976614923822238436451374541096011422736317168986779210438412206079)) (.node (.leaf 367 147738006705445142990837046831832162690119124851772396198295131250818452639190574213230966134902898664200994687) (.leaf 373 19088954112715724453072238959086421118268919561539218377790534803856983217497533031005761905696355833543533789183))) (.node (.node (.leaf 379 1226493331721899577563127456159319746963704936684770383540124080222700251359674148465142951608304698016192840859647) (.leaf 383 15833827122205044209152781856838674213649192847608917685930913014773253935317495736157193763287450056966900693336059)) (.node (.leaf 389 625506848367758437932920111494445203933108504801001635386379351870071433249344712875404877105245699770627492352622079) (.leaf 397 281162861633567742614446579132542248592527506883170751215161368256413088388501829235055641383624596202339956195298967535))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S2Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S2Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
