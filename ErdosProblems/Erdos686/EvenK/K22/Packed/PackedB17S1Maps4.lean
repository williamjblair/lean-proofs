import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s1_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (16000000 + (r.val : ZMod 307)) + 17))) = true →
      (249531871611905219958657799807306775136349031629252726644605688876139365719218549858221129215).testBit r.val = true := by decide

theorem even22_b17_s1_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (16000000 + (i : ZMod 307)) + 17))) = true) :
    (249531871611905219958657799807306775136349031629252726644605688876139365719218549858221129215).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_307_fin r
  change even22A307
    (-(33 * (46 * (16000000 + ((i % 307 : ℕ) : ZMod 307)) + 17))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (16000000 + (r.val : ZMod 311)) + 17))) = true →
      (4041478879473961822548585948695402264982093752038675808496710793151958572594207920391509245943).testBit r.val = true := by decide

theorem even22_b17_s1_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (16000000 + (i : ZMod 311)) + 17))) = true) :
    (4041478879473961822548585948695402264982093752038675808496710793151958572594207920391509245943).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_311_fin r
  change even22A311
    (-(33 * (46 * (16000000 + ((i % 311 : ℕ) : ZMod 311)) + 17))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (16000000 + (r.val : ZMod 313)) + 17))) = true →
      (8343572028776182966169326602987895974024856303854712523099321977985111224889871544535203446783).testBit r.val = true := by decide

theorem even22_b17_s1_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (16000000 + (i : ZMod 313)) + 17))) = true) :
    (8343572028776182966169326602987895974024856303854712523099321977985111224889871544535203446783).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_313_fin r
  change even22A313
    (-(33 * (46 * (16000000 + ((i % 313 : ℕ) : ZMod 313)) + 17))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (16000000 + (r.val : ZMod 317)) + 17))) = true →
      (266998377454196227662278879095532149644179485806830739102900223412886301027338702529405950507519).testBit r.val = true := by decide

theorem even22_b17_s1_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (16000000 + (i : ZMod 317)) + 17))) = true) :
    (266998377454196227662278879095532149644179485806830739102900223412886301027338702529405950507519).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_317_fin r
  change even22A317
    (-(33 * (46 * (16000000 + ((i % 317 : ℕ) : ZMod 317)) + 17))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (16000000 + (r.val : ZMod 331)) + 17))) = true →
      (1571544097609079047000510751181731770149368671690013415952266361015939448879426760379826839495702447).testBit r.val = true := by decide

theorem even22_b17_s1_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (16000000 + (i : ZMod 331)) + 17))) = true) :
    (1571544097609079047000510751181731770149368671690013415952266361015939448879426760379826839495702447).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_331_fin r
  change even22A331
    (-(33 * (46 * (16000000 + ((i % 331 : ℕ) : ZMod 331)) + 17))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (16000000 + (r.val : ZMod 337)) + 17))) = true →
      (277644105388271627645004796641016428634913284583072386980435058893753170976246093907852083734243179005).testBit r.val = true := by decide

theorem even22_b17_s1_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (16000000 + (i : ZMod 337)) + 17))) = true) :
    (277644105388271627645004796641016428634913284583072386980435058893753170976246093907852083734243179005).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_337_fin r
  change even22A337
    (-(33 * (46 * (16000000 + ((i % 337 : ℕ) : ZMod 337)) + 17))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (16000000 + (r.val : ZMod 347)) + 17))) = true →
      (286686780169390343982916172125312909090010677616520573316921905538800566746481101567335506401644980993983).testBit r.val = true := by decide

theorem even22_b17_s1_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (16000000 + (i : ZMod 347)) + 17))) = true) :
    (286686780169390343982916172125312909090010677616520573316921905538800566746481101567335506401644980993983).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_347_fin r
  change even22A347
    (-(33 * (46 * (16000000 + ((i % 347 : ℕ) : ZMod 347)) + 17))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (16000000 + (r.val : ZMod 349)) + 17))) = true →
      (1128551373287263376945219700068668562261389911071894379692275753610598646640582992104322065092332079677423).testBit r.val = true := by decide

theorem even22_b17_s1_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (16000000 + (i : ZMod 349)) + 17))) = true) :
    (1128551373287263376945219700068668562261389911071894379692275753610598646640582992104322065092332079677423).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_349_fin r
  change even22A349
    (-(33 * (46 * (16000000 + ((i % 349 : ℕ) : ZMod 349)) + 17))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB17S1Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 249531871611905219958657799807306775136349031629252726644605688876139365719218549858221129215) (.leaf 311 4041478879473961822548585948695402264982093752038675808496710793151958572594207920391509245943)) (.node (.leaf 313 8343572028776182966169326602987895974024856303854712523099321977985111224889871544535203446783) (.leaf 317 266998377454196227662278879095532149644179485806830739102900223412886301027338702529405950507519))) (.node (.node (.leaf 331 1571544097609079047000510751181731770149368671690013415952266361015939448879426760379826839495702447) (.leaf 337 277644105388271627645004796641016428634913284583072386980435058893753170976246093907852083734243179005)) (.node (.leaf 347 286686780169390343982916172125312909090010677616520573316921905538800566746481101567335506401644980993983) (.leaf 349 1128551373287263376945219700068668562261389911071894379692275753610598646640582992104322065092332079677423))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S1Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S1Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
