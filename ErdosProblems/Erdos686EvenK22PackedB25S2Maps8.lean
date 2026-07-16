import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (32000000 + (r.val : ZMod 499)) + 25))) = true →
      (1176162361002715013555485628075898917765872544913621318101566798458377312929240054801536892063458365545601478166579022262977231328188246672014185594733).testBit r.val = true := by decide

theorem even22_b25_s2_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (32000000 + (i : ZMod 499)) + 25))) = true) :
    (1176162361002715013555485628075898917765872544913621318101566798458377312929240054801536892063458365545601478166579022262977231328188246672014185594733).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_499_fin r
  change even22A499
    (-(33 * (46 * (32000000 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (32000000 + (r.val : ZMod 503)) + 25))) = true →
      (5319256616078958808455354973759269875500030750528821124443100028832305339353774020661871269102926502622688620450225528103150156099557527965597548144639).testBit r.val = true := by decide

theorem even22_b25_s2_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (32000000 + (i : ZMod 503)) + 25))) = true) :
    (5319256616078958808455354973759269875500030750528821124443100028832305339353774020661871269102926502622688620450225528103150156099557527965597548144639).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_503_fin r
  change even22A503
    (-(33 * (46 * (32000000 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (32000000 + (r.val : ZMod 509)) + 25))) = true →
      (1649776079299750402795162169788689431196933529716300936168711190587277137372381124002106395643887157007294265516285392216377122247200814146989752376458751).testBit r.val = true := by decide

theorem even22_b25_s2_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (32000000 + (i : ZMod 509)) + 25))) = true) :
    (1649776079299750402795162169788689431196933529716300936168711190587277137372381124002106395643887157007294265516285392216377122247200814146989752376458751).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_509_fin r
  change even22A509
    (-(33 * (46 * (32000000 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (32000000 + (r.val : ZMod 521)) + 25))) = true →
      (3325121200821475698681311923627194402387125305426729921337740903597443585907111040375897930689523621625969959053063446242699683393850131371915385743104431359).testBit r.val = true := by decide

theorem even22_b25_s2_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (32000000 + (i : ZMod 521)) + 25))) = true) :
    (3325121200821475698681311923627194402387125305426729921337740903597443585907111040375897930689523621625969959053063446242699683393850131371915385743104431359).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_521_fin r
  change even22A521
    (-(33 * (46 * (32000000 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (32000000 + (r.val : ZMod 523)) + 25))) = true →
      (26600671529834268624919678777739692716090950001020129283973436025458403000194952229918161246654835521914944007609820400669439978299591551418987974893482524415).testBit r.val = true := by decide

theorem even22_b25_s2_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (32000000 + (i : ZMod 523)) + 25))) = true) :
    (26600671529834268624919678777739692716090950001020129283973436025458403000194952229918161246654835521914944007609820400669439978299591551418987974893482524415).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_523_fin r
  change even22A523
    (-(33 * (46 * (32000000 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (32000000 + (r.val : ZMod 541)) + 25))) = true →
      (1739678628510541409326133336180227255059815305319970971703162179274098441378980996686102703134208316092569192521071205614062246281987916294136746195584942453291639).testBit r.val = true := by decide

theorem even22_b25_s2_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (32000000 + (i : ZMod 541)) + 25))) = true) :
    (1739678628510541409326133336180227255059815305319970971703162179274098441378980996686102703134208316092569192521071205614062246281987916294136746195584942453291639).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_541_fin r
  change even22A541
    (-(33 * (46 * (32000000 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (32000000 + (r.val : ZMod 547)) + 25))) = true →
      (453490068888087747609783200338793635360905668361623386700784827149868670576317368072035066356367499764410367813351978276939290310889601414609020814506780778785877931).testBit r.val = true := by decide

theorem even22_b25_s2_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (32000000 + (i : ZMod 547)) + 25))) = true) :
    (453490068888087747609783200338793635360905668361623386700784827149868670576317368072035066356367499764410367813351978276939290310889601414609020814506780778785877931).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_547_fin r
  change even22A547
    (-(33 * (46 * (32000000 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (32000000 + (r.val : ZMod 557)) + 25))) = true →
      (412776690309210723444022054769662371998333503153235028000487900925934131905424618617812342218780047370600395820632281036700275691596104405320850030602936377974306762751).testBit r.val = true := by decide

theorem even22_b25_s2_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (32000000 + (i : ZMod 557)) + 25))) = true) :
    (412776690309210723444022054769662371998333503153235028000487900925934131905424618617812342218780047370600395820632281036700275691596104405320850030602936377974306762751).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_557_fin r
  change even22A557
    (-(33 * (46 * (32000000 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1176162361002715013555485628075898917765872544913621318101566798458377312929240054801536892063458365545601478166579022262977231328188246672014185594733) (.leaf 503 5319256616078958808455354973759269875500030750528821124443100028832305339353774020661871269102926502622688620450225528103150156099557527965597548144639)) (.node (.leaf 509 1649776079299750402795162169788689431196933529716300936168711190587277137372381124002106395643887157007294265516285392216377122247200814146989752376458751) (.leaf 521 3325121200821475698681311923627194402387125305426729921337740903597443585907111040375897930689523621625969959053063446242699683393850131371915385743104431359))) (.node (.node (.leaf 523 26600671529834268624919678777739692716090950001020129283973436025458403000194952229918161246654835521914944007609820400669439978299591551418987974893482524415) (.leaf 541 1739678628510541409326133336180227255059815305319970971703162179274098441378980996686102703134208316092569192521071205614062246281987916294136746195584942453291639)) (.node (.leaf 547 453490068888087747609783200338793635360905668361623386700784827149868670576317368072035066356367499764410367813351978276939290310889601414609020814506780778785877931) (.leaf 557 412776690309210723444022054769662371998333503153235028000487900925934131905424618617812342218780047370600395820632281036700275691596104405320850030602936377974306762751))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
