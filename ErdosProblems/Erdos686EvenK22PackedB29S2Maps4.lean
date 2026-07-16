import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s2_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (32000000 + (r.val : ZMod 307)) + 29))) = true →
      (130370285000436657003455071237431684019159605975340590617652777800911970111704362970081394671).testBit r.val = true := by decide

theorem even22_b29_s2_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (32000000 + (i : ZMod 307)) + 29))) = true) :
    (130370285000436657003455071237431684019159605975340590617652777800911970111704362970081394671).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_307_fin r
  change even22A307
    (-(33 * (46 * (32000000 + ((i % 307 : ℕ) : ZMod 307)) + 29))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (32000000 + (r.val : ZMod 311)) + 29))) = true →
      (4170194587316581100943669133304920616960140423196121738192189239649074606260141017831770684925).testBit r.val = true := by decide

theorem even22_b29_s2_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (32000000 + (i : ZMod 311)) + 29))) = true) :
    (4170194587316581100943669133304920616960140423196121738192189239649074606260141017831770684925).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_311_fin r
  change even22A311
    (-(33 * (46 * (32000000 + ((i % 311 : ℕ) : ZMod 311)) + 29))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (32000000 + (r.val : ZMod 313)) + 29))) = true →
      (8343699359066053618040789585409855101928474051774163925517639715510057133074563335878160150527).testBit r.val = true := by decide

theorem even22_b29_s2_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (32000000 + (i : ZMod 313)) + 29))) = true) :
    (8343699359066053618040789585409855101928474051774163925517639715510057133074563335878160150527).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_313_fin r
  change even22A313
    (-(33 * (46 * (32000000 + ((i % 313 : ℕ) : ZMod 313)) + 29))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (32000000 + (r.val : ZMod 317)) + 29))) = true →
      (133466341474989786066965632602387417183666154912091730664243783123932274341975117755282569691131).testBit r.val = true := by decide

theorem even22_b29_s2_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (32000000 + (i : ZMod 317)) + 29))) = true) :
    (133466341474989786066965632602387417183666154912091730664243783123932274341975117755282569691131).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_317_fin r
  change even22A317
    (-(33 * (46 * (32000000 + ((i % 317 : ℕ) : ZMod 317)) + 29))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (32000000 + (r.val : ZMod 331)) + 29))) = true →
      (4289028067134889699182327974751291581981565492167727851588962653510106667513052859755098825259196415).testBit r.val = true := by decide

theorem even22_b29_s2_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (32000000 + (i : ZMod 331)) + 29))) = true) :
    (4289028067134889699182327974751291581981565492167727851588962653510106667513052859755098825259196415).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_331_fin r
  change even22A331
    (-(33 * (46 * (32000000 + ((i % 331 : ℕ) : ZMod 331)) + 29))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (32000000 + (r.val : ZMod 337)) + 29))) = true →
      (201226799551280339974620123114177494079777543247965703754793518127829322909532657383692061450579197171).testBit r.val = true := by decide

theorem even22_b29_s2_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (32000000 + (i : ZMod 337)) + 29))) = true) :
    (201226799551280339974620123114177494079777543247965703754793518127829322909532657383692061450579197171).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_337_fin r
  change even22A337
    (-(33 * (46 * (32000000 + ((i % 337 : ℕ) : ZMod 337)) + 29))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (32000000 + (r.val : ZMod 347)) + 29))) = true →
      (286127390543022032019121124648105263697130488778921400179735015180632901115628084914208263678025743204351).testBit r.val = true := by decide

theorem even22_b29_s2_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (32000000 + (i : ZMod 347)) + 29))) = true) :
    (286127390543022032019121124648105263697130488778921400179735015180632901115628084914208263678025743204351).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_347_fin r
  change even22A347
    (-(33 * (46 * (32000000 + ((i % 347 : ℕ) : ZMod 347)) + 29))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (32000000 + (r.val : ZMod 349)) + 29))) = true →
      (1146749286368162910195368225420546015045976069557300229972611735913699641495651099201903442260933371453207).testBit r.val = true := by decide

theorem even22_b29_s2_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (32000000 + (i : ZMod 349)) + 29))) = true) :
    (1146749286368162910195368225420546015045976069557300229972611735913699641495651099201903442260933371453207).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_349_fin r
  change even22A349
    (-(33 * (46 * (32000000 + ((i % 349 : ℕ) : ZMod 349)) + 29))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB29S2Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 130370285000436657003455071237431684019159605975340590617652777800911970111704362970081394671) (.leaf 311 4170194587316581100943669133304920616960140423196121738192189239649074606260141017831770684925)) (.node (.leaf 313 8343699359066053618040789585409855101928474051774163925517639715510057133074563335878160150527) (.leaf 317 133466341474989786066965632602387417183666154912091730664243783123932274341975117755282569691131))) (.node (.node (.leaf 331 4289028067134889699182327974751291581981565492167727851588962653510106667513052859755098825259196415) (.leaf 337 201226799551280339974620123114177494079777543247965703754793518127829322909532657383692061450579197171)) (.node (.leaf 347 286127390543022032019121124648105263697130488778921400179735015180632901115628084914208263678025743204351) (.leaf 349 1146749286368162910195368225420546015045976069557300229972611735913699641495651099201903442260933371453207))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S2Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S2Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
