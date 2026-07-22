import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s2_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (32000000 + (r.val : ZMod 307)) + 21))) = true →
      (255136238291359719500509423961853589875468493009246283363015833196750086044462824124847996671).testBit r.val = true := by decide

theorem even22_b21_s2_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (32000000 + (i : ZMod 307)) + 21))) = true) :
    (255136238291359719500509423961853589875468493009246283363015833196750086044462824124847996671).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_307_fin r
  change even22A307
    (-(33 * (46 * (32000000 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (32000000 + (r.val : ZMod 311)) + 21))) = true →
      (4171841473578209472456463932800097351177225951564116721260358481041806168122368968197129895407).testBit r.val = true := by decide

theorem even22_b21_s2_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (32000000 + (i : ZMod 311)) + 21))) = true) :
    (4171841473578209472456463932800097351177225951564116721260358481041806168122368968197129895407).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_311_fin r
  change even22A311
    (-(33 * (46 * (32000000 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (32000000 + (r.val : ZMod 313)) + 21))) = true →
      (16684339184610381638611507174279515329062796154916768673765198824378589071121808445066318970879).testBit r.val = true := by decide

theorem even22_b21_s2_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (32000000 + (i : ZMod 313)) + 21))) = true) :
    (16684339184610381638611507174279515329062796154916768673765198824378589071121808445066318970879).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_313_fin r
  change even22A313
    (-(33 * (46 * (32000000 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (32000000 + (r.val : ZMod 317)) + 21))) = true →
      (260708012395192128858686338846398441985627493695781343860197236216969060120967775867871699135999).testBit r.val = true := by decide

theorem even22_b21_s2_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (32000000 + (i : ZMod 317)) + 21))) = true) :
    (260708012395192128858686338846398441985627493695781343860197236216969060120967775867871699135999).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_317_fin r
  change even22A317
    (-(33 * (46 * (32000000 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (32000000 + (r.val : ZMod 331)) + 21))) = true →
      (4374500915862588331911091885927807551136594609851752668927612311356971812166497437006116475939749375).testBit r.val = true := by decide

theorem even22_b21_s2_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (32000000 + (i : ZMod 331)) + 21))) = true) :
    (4374500915862588331911091885927807551136594609851752668927612311356971812166497437006116475939749375).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_331_fin r
  change even22A331
    (-(33 * (46 * (32000000 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (32000000 + (r.val : ZMod 337)) + 21))) = true →
      (139403049540124288491171270428017990850029742934350894710733424128556788718441553020115442598298517119).testBit r.val = true := by decide

theorem even22_b21_s2_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (32000000 + (i : ZMod 337)) + 21))) = true) :
    (139403049540124288491171270428017990850029742934350894710733424128556788718441553020115442598298517119).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_337_fin r
  change even22A337
    (-(33 * (46 * (32000000 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (32000000 + (r.val : ZMod 347)) + 21))) = true →
      (286687326998237457489774649823215320322224739145553826565139276844641297680409159051479249281570639445503).testBit r.val = true := by decide

theorem even22_b21_s2_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (32000000 + (i : ZMod 347)) + 21))) = true) :
    (286687326998237457489774649823215320322224739145553826565139276844641297680409159051479249281570639445503).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_347_fin r
  change even22A347
    (-(33 * (46 * (32000000 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (32000000 + (r.val : ZMod 349)) + 21))) = true →
      (851942906305222276809121761944420524472669578299905120782532811594660811949233657608747336505803092262910).testBit r.val = true := by decide

theorem even22_b21_s2_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (32000000 + (i : ZMod 349)) + 21))) = true) :
    (851942906305222276809121761944420524472669578299905120782532811594660811949233657608747336505803092262910).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_349_fin r
  change even22A349
    (-(33 * (46 * (32000000 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S2Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 255136238291359719500509423961853589875468493009246283363015833196750086044462824124847996671) (.leaf 311 4171841473578209472456463932800097351177225951564116721260358481041806168122368968197129895407)) (.node (.leaf 313 16684339184610381638611507174279515329062796154916768673765198824378589071121808445066318970879) (.leaf 317 260708012395192128858686338846398441985627493695781343860197236216969060120967775867871699135999))) (.node (.node (.leaf 331 4374500915862588331911091885927807551136594609851752668927612311356971812166497437006116475939749375) (.leaf 337 139403049540124288491171270428017990850029742934350894710733424128556788718441553020115442598298517119)) (.node (.leaf 347 286687326998237457489774649823215320322224739145553826565139276844641297680409159051479249281570639445503) (.leaf 349 851942906305222276809121761944420524472669578299905120782532811594660811949233657608747336505803092262910))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S2Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S2Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
