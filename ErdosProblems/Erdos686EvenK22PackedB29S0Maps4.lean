import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (0 + (r.val : ZMod 307)) + 29))) = true →
      (178239152058983437470518625872259881817997344785220708541705051967284873039125197160586411327).testBit r.val = true := by decide

theorem even22_b29_s0_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (0 + (i : ZMod 307)) + 29))) = true) :
    (178239152058983437470518625872259881817997344785220708541705051967284873039125197160586411327).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_307_fin r
  change even22A307
    (-(33 * (46 * (0 + ((i % 307 : ℕ) : ZMod 307)) + 29))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (0 + (r.val : ZMod 311)) + 29))) = true →
      (4155553266905778951438020966307248106418005005521108988951716575565689731765518678229367382015).testBit r.val = true := by decide

theorem even22_b29_s0_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (0 + (i : ZMod 311)) + 29))) = true) :
    (4155553266905778951438020966307248106418005005521108988951716575565689731765518678229367382015).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_311_fin r
  change even22A311
    (-(33 * (46 * (0 + ((i % 311 : ℕ) : ZMod 311)) + 29))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (0 + (r.val : ZMod 313)) + 29))) = true →
      (16687398718010678391333420210488246376165499615513495350190152586428750516471803432363114692607).testBit r.val = true := by decide

theorem even22_b29_s0_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (0 + (i : ZMod 313)) + 29))) = true) :
    (16687398718010678391333420210488246376165499615513495350190152586428750516471803432363114692607).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_313_fin r
  change even22A313
    (-(33 * (46 * (0 + ((i % 313 : ℕ) : ZMod 313)) + 29))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (0 + (r.val : ZMod 317)) + 29))) = true →
      (265825040768783557119931518437316368056890668524629746500736959906962990309777133563521934030831).testBit r.val = true := by decide

theorem even22_b29_s0_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (0 + (i : ZMod 317)) + 29))) = true) :
    (265825040768783557119931518437316368056890668524629746500736959906962990309777133563521934030831).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_317_fin r
  change even22A317
    (-(33 * (46 * (0 + ((i % 317 : ℕ) : ZMod 317)) + 29))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (0 + (r.val : ZMod 331)) + 29))) = true →
      (4331781684275859182532028076566189940991085577156810157599175143808184772752015345619884691738558203).testBit r.val = true := by decide

theorem even22_b29_s0_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (0 + (i : ZMod 331)) + 29))) = true) :
    (4331781684275859182532028076566189940991085577156810157599175143808184772752015345619884691738558203).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_331_fin r
  change even22A331
    (-(33 * (46 * (0 + ((i % 331 : ℕ) : ZMod 331)) + 29))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (0 + (r.val : ZMod 337)) + 29))) = true →
      (227405440102417565702206779952926451320989788808880431133811507708484761723776561559604504080289857279).testBit r.val = true := by decide

theorem even22_b29_s0_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (0 + (i : ZMod 337)) + 29))) = true) :
    (227405440102417565702206779952926451320989788808880431133811507708484761723776561559604504080289857279).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_337_fin r
  change even22A337
    (-(33 * (46 * (0 + ((i % 337 : ℕ) : ZMod 337)) + 29))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (0 + (r.val : ZMod 347)) + 29))) = true →
      (215015460664434851625722242036843568087233360655476383671859117853610684895698540907113220164049856102399).testBit r.val = true := by decide

theorem even22_b29_s0_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (0 + (i : ZMod 347)) + 29))) = true) :
    (215015460664434851625722242036843568087233360655476383671859117853610684895698540907113220164049856102399).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_347_fin r
  change even22A347
    (-(33 * (46 * (0 + ((i % 347 : ℕ) : ZMod 347)) + 29))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (0 + (r.val : ZMod 349)) + 29))) = true →
      (562175926013611695147192531643622736332852926460942079450016527171140434671278341180523042296796477915124).testBit r.val = true := by decide

theorem even22_b29_s0_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (0 + (i : ZMod 349)) + 29))) = true) :
    (562175926013611695147192531643622736332852926460942079450016527171140434671278341180523042296796477915124).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_349_fin r
  change even22A349
    (-(33 * (46 * (0 + ((i % 349 : ℕ) : ZMod 349)) + 29))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 178239152058983437470518625872259881817997344785220708541705051967284873039125197160586411327) (.leaf 311 4155553266905778951438020966307248106418005005521108988951716575565689731765518678229367382015)) (.node (.leaf 313 16687398718010678391333420210488246376165499615513495350190152586428750516471803432363114692607) (.leaf 317 265825040768783557119931518437316368056890668524629746500736959906962990309777133563521934030831))) (.node (.node (.leaf 331 4331781684275859182532028076566189940991085577156810157599175143808184772752015345619884691738558203) (.leaf 337 227405440102417565702206779952926451320989788808880431133811507708484761723776561559604504080289857279)) (.node (.leaf 347 215015460664434851625722242036843568087233360655476383671859117853610684895698540907113220164049856102399) (.leaf 349 562175926013611695147192531643622736332852926460942079450016527171140434671278341180523042296796477915124))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
