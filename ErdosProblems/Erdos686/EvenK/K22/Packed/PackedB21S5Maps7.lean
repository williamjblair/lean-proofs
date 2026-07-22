import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s5_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (80000000 + (r.val : ZMod 449)) + 21))) = true →
      (1436597802577302167930327986374288928621265598427822592711850598480335476252376577946876822938624567484206525341971571402382220918259647).testBit r.val = true := by decide

theorem even22_b21_s5_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (80000000 + (i : ZMod 449)) + 21))) = true) :
    (1436597802577302167930327986374288928621265598427822592711850598480335476252376577946876822938624567484206525341971571402382220918259647).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_449_fin r
  change even22A449
    (-(33 * (46 * (80000000 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (80000000 + (r.val : ZMod 457)) + 21))) = true →
      (371959001809493098196423222726612857972307472471597519833306740787892931813342566065189261488445047378040546168253530540708032467498956797).testBit r.val = true := by decide

theorem even22_b21_s5_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (80000000 + (i : ZMod 457)) + 21))) = true) :
    (371959001809493098196423222726612857972307472471597519833306740787892931813342566065189261488445047378040546168253530540708032467498956797).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_457_fin r
  change even22A457
    (-(33 * (46 * (80000000 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (80000000 + (r.val : ZMod 461)) + 21))) = true →
      (4465697102228937146461297322243473663707687818167289536258677901862448966058924597838579179125561626403059515068620284776642782440391177855).testBit r.val = true := by decide

theorem even22_b21_s5_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (80000000 + (i : ZMod 461)) + 21))) = true) :
    (4465697102228937146461297322243473663707687818167289536258677901862448966058924597838579179125561626403059515068620284776642782440391177855).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_461_fin r
  change even22A461
    (-(33 * (46 * (80000000 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (80000000 + (r.val : ZMod 463)) + 21))) = true →
      (23817051045124920676684846825813830774254765979542146868212189099674724672315517732617158841047396387644273148341155423584496950508506568423).testBit r.val = true := by decide

theorem even22_b21_s5_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (80000000 + (i : ZMod 463)) + 21))) = true) :
    (23817051045124920676684846825813830774254765979542146868212189099674724672315517732617158841047396387644273148341155423584496950508506568423).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_463_fin r
  change even22A463
    (-(33 * (46 * (80000000 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (80000000 + (r.val : ZMod 467)) + 21))) = true →
      (380699017238757940484249455872955425490991660787622677844304165877985913688153919023712585545696048523474886642523011920473080046487629330429).testBit r.val = true := by decide

theorem even22_b21_s5_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (80000000 + (i : ZMod 467)) + 21))) = true) :
    (380699017238757940484249455872955425490991660787622677844304165877985913688153919023712585545696048523474886642523011920473080046487629330429).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_467_fin r
  change even22A467
    (-(33 * (46 * (80000000 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (80000000 + (r.val : ZMod 479)) + 21))) = true →
      (1558560645729607490291664316776530910181670741509083174314368865529469744000738614425714599293649608678586359357809363602914002047760328249962383).testBit r.val = true := by decide

theorem even22_b21_s5_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (80000000 + (i : ZMod 479)) + 21))) = true) :
    (1558560645729607490291664316776530910181670741509083174314368865529469744000738614425714599293649608678586359357809363602914002047760328249962383).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_479_fin r
  change even22A479
    (-(33 * (46 * (80000000 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (80000000 + (r.val : ZMod 487)) + 21))) = true →
      (399483115851464815719188455579449419862151087680056976245988358813449335812950450926032731849926281938834982312356117597587061982774802819967614975).testBit r.val = true := by decide

theorem even22_b21_s5_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (80000000 + (i : ZMod 487)) + 21))) = true) :
    (399483115851464815719188455579449419862151087680056976245988358813449335812950450926032731849926281938834982312356117597587061982774802819967614975).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_487_fin r
  change even22A487
    (-(33 * (46 * (80000000 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (80000000 + (r.val : ZMod 491)) + 21))) = true →
      (5393947054066288114233145692167917725125279761740421438771238581158734466828841659659988805443779373508998695428455278449864413660926732519155105591).testBit r.val = true := by decide

theorem even22_b21_s5_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (80000000 + (i : ZMod 491)) + 21))) = true) :
    (5393947054066288114233145692167917725125279761740421438771238581158734466828841659659988805443779373508998695428455278449864413660926732519155105591).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_491_fin r
  change even22A491
    (-(33 * (46 * (80000000 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S5Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1436597802577302167930327986374288928621265598427822592711850598480335476252376577946876822938624567484206525341971571402382220918259647) (.leaf 457 371959001809493098196423222726612857972307472471597519833306740787892931813342566065189261488445047378040546168253530540708032467498956797)) (.node (.leaf 461 4465697102228937146461297322243473663707687818167289536258677901862448966058924597838579179125561626403059515068620284776642782440391177855) (.leaf 463 23817051045124920676684846825813830774254765979542146868212189099674724672315517732617158841047396387644273148341155423584496950508506568423))) (.node (.node (.leaf 467 380699017238757940484249455872955425490991660787622677844304165877985913688153919023712585545696048523474886642523011920473080046487629330429) (.leaf 479 1558560645729607490291664316776530910181670741509083174314368865529469744000738614425714599293649608678586359357809363602914002047760328249962383)) (.node (.leaf 487 399483115851464815719188455579449419862151087680056976245988358813449335812950450926032731849926281938834982312356117597587061982774802819967614975) (.leaf 491 5393947054066288114233145692167917725125279761740421438771238581158734466828841659659988805443779373508998695428455278449864413660926732519155105591))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S5Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S5Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
