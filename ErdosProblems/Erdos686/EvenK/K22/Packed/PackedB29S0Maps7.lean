import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (0 + (r.val : ZMod 449)) + 29))) = true →
      (704068867567010429963233685910422618701530478405353189330059986263064141132896013915417124466863872331367990789813559467516292627398655).testBit r.val = true := by decide

theorem even22_b29_s0_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (0 + (i : ZMod 449)) + 29))) = true) :
    (704068867567010429963233685910422618701530478405353189330059986263064141132896013915417124466863872331367990789813559467516292627398655).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_449_fin r
  change even22A449
    (-(33 * (46 * (0 + ((i % 449 : ℕ) : ZMod 449)) + 29))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (0 + (r.val : ZMod 457)) + 29))) = true →
      (348879726264048382107307843284176002404333695726801468551598561221303132801417330160484682357843605581078040071416858857867526667910512111).testBit r.val = true := by decide

theorem even22_b29_s0_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (0 + (i : ZMod 457)) + 29))) = true) :
    (348879726264048382107307843284176002404333695726801468551598561221303132801417330160484682357843605581078040071416858857867526667910512111).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_457_fin r
  change even22A457
    (-(33 * (46 * (0 + ((i % 457 : ℕ) : ZMod 457)) + 29))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (0 + (r.val : ZMod 461)) + 29))) = true →
      (5733281143533310130642248954748753975668630637601555960269230639473524773912131408808963245671946766045658803830771893884617561293453000703).testBit r.val = true := by decide

theorem even22_b29_s0_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (0 + (i : ZMod 461)) + 29))) = true) :
    (5733281143533310130642248954748753975668630637601555960269230639473524773912131408808963245671946766045658803830771893884617561293453000703).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_461_fin r
  change even22A461
    (-(33 * (46 * (0 + ((i % 461 : ℕ) : ZMod 461)) + 29))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (0 + (r.val : ZMod 463)) + 29))) = true →
      (11720864630828255779814882127982143431977388536525045888881028175228157446358236264504055923485520426572313864403500249383601903658799724415).testBit r.val = true := by decide

theorem even22_b29_s0_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (0 + (i : ZMod 463)) + 29))) = true) :
    (11720864630828255779814882127982143431977388536525045888881028175228157446358236264504055923485520426572313864403500249383601903658799724415).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_463_fin r
  change even22A463
    (-(33 * (46 * (0 + ((i % 463 : ℕ) : ZMod 463)) + 29))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (0 + (r.val : ZMod 467)) + 29))) = true →
      (163695664681258687605289480101367960004770206534588576644252992448138357469771458701088848314078558532648651836261828857483660449145213335542).testBit r.val = true := by decide

theorem even22_b29_s0_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (0 + (i : ZMod 467)) + 29))) = true) :
    (163695664681258687605289480101367960004770206534588576644252992448138357469771458701088848314078558532648651836261828857483660449145213335542).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_467_fin r
  change even22A467
    (-(33 * (46 * (0 + ((i % 467 : ℕ) : ZMod 467)) + 29))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (0 + (r.val : ZMod 479)) + 29))) = true →
      (1536485425617706380144229155543663727744165538314059004408731473885661885405397635631838342190129257299763435296677466612249894585644386183249791).testBit r.val = true := by decide

theorem even22_b29_s0_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (0 + (i : ZMod 479)) + 29))) = true) :
    (1536485425617706380144229155543663727744165538314059004408731473885661885405397635631838342190129257299763435296677466612249894585644386183249791).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_479_fin r
  change even22A479
    (-(33 * (46 * (0 + ((i % 479 : ℕ) : ZMod 479)) + 29))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (0 + (r.val : ZMod 487)) + 29))) = true →
      (399169200873074131446022967958105039723895109520509679076480567222090064892202086200631901696332255519762131697523134036874795618757656827142336380).testBit r.val = true := by decide

theorem even22_b29_s0_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (0 + (i : ZMod 487)) + 29))) = true) :
    (399169200873074131446022967958105039723895109520509679076480567222090064892202086200631901696332255519762131697523134036874795618757656827142336380).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_487_fin r
  change even22A487
    (-(33 * (46 * (0 + ((i % 487 : ℕ) : ZMod 487)) + 29))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (0 + (r.val : ZMod 491)) + 29))) = true →
      (4782128363931306585702699803921566150742745572430623026539419173909778980394142262809781774023167646227132707930174832975363889253343528151164873983).testBit r.val = true := by decide

theorem even22_b29_s0_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (0 + (i : ZMod 491)) + 29))) = true) :
    (4782128363931306585702699803921566150742745572430623026539419173909778980394142262809781774023167646227132707930174832975363889253343528151164873983).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_491_fin r
  change even22A491
    (-(33 * (46 * (0 + ((i % 491 : ℕ) : ZMod 491)) + 29))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 704068867567010429963233685910422618701530478405353189330059986263064141132896013915417124466863872331367990789813559467516292627398655) (.leaf 457 348879726264048382107307843284176002404333695726801468551598561221303132801417330160484682357843605581078040071416858857867526667910512111)) (.node (.leaf 461 5733281143533310130642248954748753975668630637601555960269230639473524773912131408808963245671946766045658803830771893884617561293453000703) (.leaf 463 11720864630828255779814882127982143431977388536525045888881028175228157446358236264504055923485520426572313864403500249383601903658799724415))) (.node (.node (.leaf 467 163695664681258687605289480101367960004770206534588576644252992448138357469771458701088848314078558532648651836261828857483660449145213335542) (.leaf 479 1536485425617706380144229155543663727744165538314059004408731473885661885405397635631838342190129257299763435296677466612249894585644386183249791)) (.node (.leaf 487 399169200873074131446022967958105039723895109520509679076480567222090064892202086200631901696332255519762131697523134036874795618757656827142336380) (.leaf 491 4782128363931306585702699803921566150742745572430623026539419173909778980394142262809781774023167646227132707930174832975363889253343528151164873983))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
