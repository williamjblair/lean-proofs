import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (32000000 + (r.val : ZMod 449)) + 25))) = true →
      (1090257983551192725116716534456272831912765610165693893092098893029189726381298462695421634809208705946399255063745395279052427419970943).testBit r.val = true := by decide

theorem even22_b25_s2_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (32000000 + (i : ZMod 449)) + 25))) = true) :
    (1090257983551192725116716534456272831912765610165693893092098893029189726381298462695421634809208705946399255063745395279052427419970943).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_449_fin r
  change even22A449
    (-(33 * (46 * (32000000 + ((i % 449 : ℕ) : ZMod 449)) + 25))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (32000000 + (r.val : ZMod 457)) + 25))) = true →
      (185343844195843889496411323676209877558885123215457990740886042969301928467681984821223356437700999203177032343544645906246250144804632575).testBit r.val = true := by decide

theorem even22_b25_s2_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (32000000 + (i : ZMod 457)) + 25))) = true) :
    (185343844195843889496411323676209877558885123215457990740886042969301928467681984821223356437700999203177032343544645906246250144804632575).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_457_fin r
  change even22A457
    (-(33 * (46 * (32000000 + ((i % 457 : ℕ) : ZMod 457)) + 25))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (32000000 + (r.val : ZMod 461)) + 25))) = true →
      (5942396335491345221803893776892966230929745557710168046208894734887520065363141886502887400247943623041387622041756980115708778160966336463).testBit r.val = true := by decide

theorem even22_b25_s2_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (32000000 + (i : ZMod 461)) + 25))) = true) :
    (5942396335491345221803893776892966230929745557710168046208894734887520065363141886502887400247943623041387622041756980115708778160966336463).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_461_fin r
  change even22A461
    (-(33 * (46 * (32000000 + ((i % 461 : ℕ) : ZMod 461)) + 25))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (32000000 + (r.val : ZMod 463)) + 25))) = true →
      (23811167035922105769789761577860686168889972955839287909115622849936864727059269674605175775218193401893409484044953459144454008039061569023).testBit r.val = true := by decide

theorem even22_b25_s2_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (32000000 + (i : ZMod 463)) + 25))) = true) :
    (23811167035922105769789761577860686168889972955839287909115622849936864727059269674605175775218193401893409484044953459144454008039061569023).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_463_fin r
  change even22A463
    (-(33 * (46 * (32000000 + ((i % 463 : ℕ) : ZMod 463)) + 25))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (32000000 + (r.val : ZMod 467)) + 25))) = true →
      (353441320127806432835649824565386044078963671201527198075496035797337765983336037601647893422240906270421900149398675730251878166219409289215).testBit r.val = true := by decide

theorem even22_b25_s2_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (32000000 + (i : ZMod 467)) + 25))) = true) :
    (353441320127806432835649824565386044078963671201527198075496035797337765983336037601647893422240906270421900149398675730251878166219409289215).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_467_fin r
  change even22A467
    (-(33 * (46 * (32000000 + ((i % 467 : ℕ) : ZMod 467)) + 25))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (32000000 + (r.val : ZMod 479)) + 25))) = true →
      (1556175884332032275331315538017292807120448807015200393137228421631334554706884286668576990945323817602325871926651903084510448155734473180708317).testBit r.val = true := by decide

theorem even22_b25_s2_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (32000000 + (i : ZMod 479)) + 25))) = true) :
    (1556175884332032275331315538017292807120448807015200393137228421631334554706884286668576990945323817602325871926651903084510448155734473180708317).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_479_fin r
  change even22A479
    (-(33 * (46 * (32000000 + ((i % 479 : ℕ) : ZMod 479)) + 25))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (32000000 + (r.val : ZMod 487)) + 25))) = true →
      (193548219211033777060305377892772258392653608822772086378031929790222725068107932014204582444700231007170875034504207377666070597895725115302707191).testBit r.val = true := by decide

theorem even22_b25_s2_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (32000000 + (i : ZMod 487)) + 25))) = true) :
    (193548219211033777060305377892772258392653608822772086378031929790222725068107932014204582444700231007170875034504207377666070597895725115302707191).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_487_fin r
  change even22A487
    (-(33 * (46 * (32000000 + ((i % 487 : ℕ) : ZMod 487)) + 25))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (32000000 + (r.val : ZMod 491)) + 25))) = true →
      (2696702676316199399722709135968538614212383449638428130857242483366517597261712542127738187353438249422946802224927689567175515110098894456268103150).testBit r.val = true := by decide

theorem even22_b25_s2_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (32000000 + (i : ZMod 491)) + 25))) = true) :
    (2696702676316199399722709135968538614212383449638428130857242483366517597261712542127738187353438249422946802224927689567175515110098894456268103150).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_491_fin r
  change even22A491
    (-(33 * (46 * (32000000 + ((i % 491 : ℕ) : ZMod 491)) + 25))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1090257983551192725116716534456272831912765610165693893092098893029189726381298462695421634809208705946399255063745395279052427419970943) (.leaf 457 185343844195843889496411323676209877558885123215457990740886042969301928467681984821223356437700999203177032343544645906246250144804632575)) (.node (.leaf 461 5942396335491345221803893776892966230929745557710168046208894734887520065363141886502887400247943623041387622041756980115708778160966336463) (.leaf 463 23811167035922105769789761577860686168889972955839287909115622849936864727059269674605175775218193401893409484044953459144454008039061569023))) (.node (.node (.leaf 467 353441320127806432835649824565386044078963671201527198075496035797337765983336037601647893422240906270421900149398675730251878166219409289215) (.leaf 479 1556175884332032275331315538017292807120448807015200393137228421631334554706884286668576990945323817602325871926651903084510448155734473180708317)) (.node (.leaf 487 193548219211033777060305377892772258392653608822772086378031929790222725068107932014204582444700231007170875034504207377666070597895725115302707191) (.leaf 491 2696702676316199399722709135968538614212383449638428130857242483366517597261712542127738187353438249422946802224927689567175515110098894456268103150))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
