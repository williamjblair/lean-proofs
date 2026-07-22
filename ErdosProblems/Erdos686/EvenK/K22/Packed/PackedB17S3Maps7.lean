import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s3_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (48000000 + (r.val : ZMod 449)) + 17))) = true →
      (1453411269169651850642523197843019733685531696347741349585478485784144529682664080196204970440272873427458534252772273093998504124612542).testBit r.val = true := by decide

theorem even22_b17_s3_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (48000000 + (i : ZMod 449)) + 17))) = true) :
    (1453411269169651850642523197843019733685531696347741349585478485784144529682664080196204970440272873427458534252772273093998504124612542).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_449_fin r
  change even22A449
    (-(33 * (46 * (48000000 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (48000000 + (r.val : ZMod 457)) + 17))) = true →
      (348876909231628826343487121382700282640598686736442323787364186554825277168098267547612811348418833219857852051545476584590080279238410223).testBit r.val = true := by decide

theorem even22_b17_s3_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (48000000 + (i : ZMod 457)) + 17))) = true) :
    (348876909231628826343487121382700282640598686736442323787364186554825277168098267547612811348418833219857852051545476584590080279238410223).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_457_fin r
  change even22A457
    (-(33 * (46 * (48000000 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (48000000 + (r.val : ZMod 461)) + 17))) = true →
      (5953897990350919112439201202744532205394178862275715384881230401723322941243092445718527120664658739843507293911833286664589041236919189375).testBit r.val = true := by decide

theorem even22_b17_s3_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (48000000 + (i : ZMod 461)) + 17))) = true) :
    (5953897990350919112439201202744532205394178862275715384881230401723322941243092445718527120664658739843507293911833286664589041236919189375).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_461_fin r
  change even22A461
    (-(33 * (46 * (48000000 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (48000000 + (r.val : ZMod 463)) + 17))) = true →
      (23817047768349180838366722715073903225072466782482695724069316120575368382026964690129591856087818614710784707827364763324565411624421916639).testBit r.val = true := by decide

theorem even22_b17_s3_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (48000000 + (i : ZMod 463)) + 17))) = true) :
    (23817047768349180838366722715073903225072466782482695724069316120575368382026964690129591856087818614710784707827364763324565411624421916639).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_463_fin r
  change even22A463
    (-(33 * (46 * (48000000 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (48000000 + (r.val : ZMod 467)) + 17))) = true →
      (333438711860194676931190777824233068815688763678467711133413826475924928515792470668588027390567358874229996664639154987308731458018313502682).testBit r.val = true := by decide

theorem even22_b17_s3_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (48000000 + (i : ZMod 467)) + 17))) = true) :
    (333438711860194676931190777824233068815688763678467711133413826475924928515792470668588027390567358874229996664639154987308731458018313502682).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_467_fin r
  change even22A467
    (-(33 * (46 * (48000000 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (48000000 + (r.val : ZMod 479)) + 17))) = true →
      (1553436455198693437330355488380834567857000040372699219141930733163006494957977192413327992499376432007070413111515421269348510873389128336015359).testBit r.val = true := by decide

theorem even22_b17_s3_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (48000000 + (i : ZMod 479)) + 17))) = true) :
    (1553436455198693437330355488380834567857000040372699219141930733163006494957977192413327992499376432007070413111515421269348510873389128336015359).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_479_fin r
  change even22A479
    (-(33 * (46 * (48000000 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (48000000 + (r.val : ZMod 487)) + 17))) = true →
      (187198021255327403016624615398029595085683503191497331673575948183822658816509500390832903661477095134047716751128010244991763981227770186081238523).testBit r.val = true := by decide

theorem even22_b17_s3_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (48000000 + (i : ZMod 487)) + 17))) = true) :
    (187198021255327403016624615398029595085683503191497331673575948183822658816509500390832903661477095134047716751128010244991763981227770186081238523).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_487_fin r
  change even22A487
    (-(33 * (46 * (48000000 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (48000000 + (r.val : ZMod 491)) + 17))) = true →
      (3188858230728061473398020336059517317767644271545420432102114890259809128150841945745423983844337326181126740662481652920652869177216543487916242422).testBit r.val = true := by decide

theorem even22_b17_s3_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (48000000 + (i : ZMod 491)) + 17))) = true) :
    (3188858230728061473398020336059517317767644271545420432102114890259809128150841945745423983844337326181126740662481652920652869177216543487916242422).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_491_fin r
  change even22A491
    (-(33 * (46 * (48000000 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S3Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1453411269169651850642523197843019733685531696347741349585478485784144529682664080196204970440272873427458534252772273093998504124612542) (.leaf 457 348876909231628826343487121382700282640598686736442323787364186554825277168098267547612811348418833219857852051545476584590080279238410223)) (.node (.leaf 461 5953897990350919112439201202744532205394178862275715384881230401723322941243092445718527120664658739843507293911833286664589041236919189375) (.leaf 463 23817047768349180838366722715073903225072466782482695724069316120575368382026964690129591856087818614710784707827364763324565411624421916639))) (.node (.node (.leaf 467 333438711860194676931190777824233068815688763678467711133413826475924928515792470668588027390567358874229996664639154987308731458018313502682) (.leaf 479 1553436455198693437330355488380834567857000040372699219141930733163006494957977192413327992499376432007070413111515421269348510873389128336015359)) (.node (.leaf 487 187198021255327403016624615398029595085683503191497331673575948183822658816509500390832903661477095134047716751128010244991763981227770186081238523) (.leaf 491 3188858230728061473398020336059517317767644271545420432102114890259809128150841945745423983844337326181126740662481652920652869177216543487916242422))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S3Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S3Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
