import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (0 + (r.val : ZMod 449)) + 17))) = true →
      (1453655007285299288299647004453406771219186959626221073536298675023738873724690337579650302707217844652690649710714131428717232756015070).testBit r.val = true := by decide

theorem even22_b17_s0_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (0 + (i : ZMod 449)) + 17))) = true) :
    (1453655007285299288299647004453406771219186959626221073536298675023738873724690337579650302707217844652690649710714131428717232756015070).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_449_fin r
  change even22A449
    (-(33 * (46 * (0 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (0 + (r.val : ZMod 457)) + 17))) = true →
      (360148583729458095141425528243128887956956990867336762469398131021783378932883594626621114755707910795874444243932585915148785490910445559).testBit r.val = true := by decide

theorem even22_b17_s0_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (0 + (i : ZMod 457)) + 17))) = true) :
    (360148583729458095141425528243128887956956990867336762469398131021783378932883594626621114755707910795874444243932585915148785490910445559).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_457_fin r
  change even22A457
    (-(33 * (46 * (0 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (0 + (r.val : ZMod 461)) + 17))) = true →
      (5954250757214932696612751728759657582856312493281983249413431493698199628997461361473092583610555203443306571425383382841041572857284263535).testBit r.val = true := by decide

theorem even22_b17_s0_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (0 + (i : ZMod 461)) + 17))) = true) :
    (5954250757214932696612751728759657582856312493281983249413431493698199628997461361473092583610555203443306571425383382841041572857284263535).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_461_fin r
  change even22A461
    (-(33 * (46 * (0 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (0 + (r.val : ZMod 463)) + 17))) = true →
      (23718201204067857834648299027196627520411483318166856948547416706848805573441985816989013434665509393355829549399250605758600038701824860094).testBit r.val = true := by decide

theorem even22_b17_s0_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (0 + (i : ZMod 463)) + 17))) = true) :
    (23718201204067857834648299027196627520411483318166856948547416706848805573441985816989013434665509393355829549399250605758600038701824860094).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_463_fin r
  change even22A463
    (-(33 * (46 * (0 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (0 + (r.val : ZMod 467)) + 17))) = true →
      (166610696077796598651338943575540495955630684473005909195007359444522431124651268183048208612015196704317304166203734922730723721479037382582).testBit r.val = true := by decide

theorem even22_b17_s0_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (0 + (i : ZMod 467)) + 17))) = true) :
    (166610696077796598651338943575540495955630684473005909195007359444522431124651268183048208612015196704317304166203734922730723721479037382582).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_467_fin r
  change even22A467
    (-(33 * (46 * (0 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (0 + (r.val : ZMod 479)) + 17))) = true →
      (1554753289971038119322975448874296448591126309830568081412867699432221781576224089050232730642253878280182901428372345378953726277226429799202783).testBit r.val = true := by decide

theorem even22_b17_s0_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (0 + (i : ZMod 479)) + 17))) = true) :
    (1554753289971038119322975448874296448591126309830568081412867699432221781576224089050232730642253878280182901428372345378953726277226429799202783).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_479_fin r
  change even22A479
    (-(33 * (46 * (0 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (0 + (r.val : ZMod 487)) + 17))) = true →
      (98286252844669046711928530313742611442510219882007604359888200957374983495746405103082677093759782959745515599717469851493334643076987144699371007).testBit r.val = true := by decide

theorem even22_b17_s0_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (0 + (i : ZMod 487)) + 17))) = true) :
    (98286252844669046711928530313742611442510219882007604359888200957374983495746405103082677093759782959745515599717469851493334643076987144699371007).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_487_fin r
  change even22A487
    (-(33 * (46 * (0 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (0 + (r.val : ZMod 491)) + 17))) = true →
      (6373720138879738774888186415333059521198543655341446286207072696029972994423813164025273585118390006433150992948311827355776670967886297173728419581).testBit r.val = true := by decide

theorem even22_b17_s0_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (0 + (i : ZMod 491)) + 17))) = true) :
    (6373720138879738774888186415333059521198543655341446286207072696029972994423813164025273585118390006433150992948311827355776670967886297173728419581).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_491_fin r
  change even22A491
    (-(33 * (46 * (0 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453655007285299288299647004453406771219186959626221073536298675023738873724690337579650302707217844652690649710714131428717232756015070) (.leaf 457 360148583729458095141425528243128887956956990867336762469398131021783378932883594626621114755707910795874444243932585915148785490910445559)) (.node (.leaf 461 5954250757214932696612751728759657582856312493281983249413431493698199628997461361473092583610555203443306571425383382841041572857284263535) (.leaf 463 23718201204067857834648299027196627520411483318166856948547416706848805573441985816989013434665509393355829549399250605758600038701824860094))) (.node (.node (.leaf 467 166610696077796598651338943575540495955630684473005909195007359444522431124651268183048208612015196704317304166203734922730723721479037382582) (.leaf 479 1554753289971038119322975448874296448591126309830568081412867699432221781576224089050232730642253878280182901428372345378953726277226429799202783)) (.node (.leaf 487 98286252844669046711928530313742611442510219882007604359888200957374983495746405103082677093759782959745515599717469851493334643076987144699371007) (.leaf 491 6373720138879738774888186415333059521198543655341446286207072696029972994423813164025273585118390006433150992948311827355776670967886297173728419581))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
