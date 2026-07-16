import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_257_fin : ∀ r : Fin 257,
    even22A257 (-(33 * (46 * (0 + (r.val : ZMod 257)) + 17))) = true →
      (231358021807701134804540197275400065808365113467148439291186951745280929693695).testBit r.val = true := by decide

theorem even22_b17_s0_map_257 (i : ℕ)
    (h : even22A257 (-(33 * (46 * (0 + (i : ZMod 257)) + 17))) = true) :
    (231358021807701134804540197275400065808365113467148439291186951745280929693695).testBit (i % 257) = true := by
  let r : Fin 257 := ⟨i % 257, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_257_fin r
  change even22A257
    (-(33 * (46 * (0 + ((i % 257 : ℕ) : ZMod 257)) + 17))) = true
  have hcast : (i : ZMod 257) = ((i % 257 : ℕ) : ZMod 257) :=
    (ZMod.natCast_mod i 257).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_263_fin : ∀ r : Fin 263,
    even22A263 (-(33 * (46 * (0 + (r.val : ZMod 263)) + 17))) = true →
      (14691120880271870432578865164240856359125270499464608419148410077277842015518207).testBit r.val = true := by decide

theorem even22_b17_s0_map_263 (i : ℕ)
    (h : even22A263 (-(33 * (46 * (0 + (i : ZMod 263)) + 17))) = true) :
    (14691120880271870432578865164240856359125270499464608419148410077277842015518207).testBit (i % 263) = true := by
  let r : Fin 263 := ⟨i % 263, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_263_fin r
  change even22A263
    (-(33 * (46 * (0 + ((i % 263 : ℕ) : ZMod 263)) + 17))) = true
  have hcast : (i : ZMod 263) = ((i % 263 : ℕ) : ZMod 263) :=
    (ZMod.natCast_mod i 263).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_269_fin : ∀ r : Fin 269,
    even22A269 (-(33 * (46 * (0 + (r.val : ZMod 269)) + 17))) = true →
      (948566977829834228242574032216064942829482460889802769267893618039833870706146303).testBit r.val = true := by decide

theorem even22_b17_s0_map_269 (i : ℕ)
    (h : even22A269 (-(33 * (46 * (0 + (i : ZMod 269)) + 17))) = true) :
    (948566977829834228242574032216064942829482460889802769267893618039833870706146303).testBit (i % 269) = true := by
  let r : Fin 269 := ⟨i % 269, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_269_fin r
  change even22A269
    (-(33 * (46 * (0 + ((i % 269 : ℕ) : ZMod 269)) + 17))) = true
  have hcast : (i : ZMod 269) = ((i % 269 : ℕ) : ZMod 269) :=
    (ZMod.natCast_mod i 269).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_271_fin : ∀ r : Fin 271,
    even22A271 (-(33 * (46 * (0 + (r.val : ZMod 271)) + 17))) = true →
      (3794275180128377091639574036761691478339887928951830933296806959309512658856574943).testBit r.val = true := by decide

theorem even22_b17_s0_map_271 (i : ℕ)
    (h : even22A271 (-(33 * (46 * (0 + (i : ZMod 271)) + 17))) = true) :
    (3794275180128377091639574036761691478339887928951830933296806959309512658856574943).testBit (i % 271) = true := by
  let r : Fin 271 := ⟨i % 271, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_271_fin r
  change even22A271
    (-(33 * (46 * (0 + ((i % 271 : ℕ) : ZMod 271)) + 17))) = true
  have hcast : (i : ZMod 271) = ((i % 271 : ℕ) : ZMod 271) :=
    (ZMod.natCast_mod i 271).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_277_fin : ∀ r : Fin 277,
    even22A277 (-(33 * (46 * (0 + (r.val : ZMod 277)) + 17))) = true →
      (209570712451653786824355420371829050542966849305328221352663571009991719434858790911).testBit r.val = true := by decide

theorem even22_b17_s0_map_277 (i : ℕ)
    (h : even22A277 (-(33 * (46 * (0 + (i : ZMod 277)) + 17))) = true) :
    (209570712451653786824355420371829050542966849305328221352663571009991719434858790911).testBit (i % 277) = true := by
  let r : Fin 277 := ⟨i % 277, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_277_fin r
  change even22A277
    (-(33 * (46 * (0 + ((i % 277 : ℕ) : ZMod 277)) + 17))) = true
  have hcast : (i : ZMod 277) = ((i % 277 : ℕ) : ZMod 277) :=
    (ZMod.natCast_mod i 277).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_281_fin : ∀ r : Fin 281,
    even22A281 (-(33 * (46 * (0 + (r.val : ZMod 281)) + 17))) = true →
      (3885337755499833120890522110100353550143810700370339100409353039196560543627715018743).testBit r.val = true := by decide

theorem even22_b17_s0_map_281 (i : ℕ)
    (h : even22A281 (-(33 * (46 * (0 + (i : ZMod 281)) + 17))) = true) :
    (3885337755499833120890522110100353550143810700370339100409353039196560543627715018743).testBit (i % 281) = true := by
  let r : Fin 281 := ⟨i % 281, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_281_fin r
  change even22A281
    (-(33 * (46 * (0 + ((i % 281 : ℕ) : ZMod 281)) + 17))) = true
  have hcast : (i : ZMod 281) = ((i % 281 : ℕ) : ZMod 281) :=
    (ZMod.natCast_mod i 281).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_283_fin : ∀ r : Fin 283,
    even22A283 (-(33 * (46 * (0 + (r.val : ZMod 283)) + 17))) = true →
      (15298517526277616433382158763494365299079639103769163866072778674517223287256990612479).testBit r.val = true := by decide

theorem even22_b17_s0_map_283 (i : ℕ)
    (h : even22A283 (-(33 * (46 * (0 + (i : ZMod 283)) + 17))) = true) :
    (15298517526277616433382158763494365299079639103769163866072778674517223287256990612479).testBit (i % 283) = true := by
  let r : Fin 283 := ⟨i % 283, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_283_fin r
  change even22A283
    (-(33 * (46 * (0 + ((i % 283 : ℕ) : ZMod 283)) + 17))) = true
  have hcast : (i : ZMod 283) = ((i % 283 : ℕ) : ZMod 283) :=
    (ZMod.natCast_mod i 283).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_293_fin : ∀ r : Fin 293,
    even22A293 (-(33 * (46 * (0 + (r.val : ZMod 293)) + 17))) = true →
      (15898316546752310228922859257391317550145303335935861122357080606739715736369045918711287).testBit r.val = true := by decide

theorem even22_b17_s0_map_293 (i : ℕ)
    (h : even22A293 (-(33 * (46 * (0 + (i : ZMod 293)) + 17))) = true) :
    (15898316546752310228922859257391317550145303335935861122357080606739715736369045918711287).testBit (i % 293) = true := by
  let r : Fin 293 := ⟨i % 293, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_293_fin r
  change even22A293
    (-(33 * (46 * (0 + ((i % 293 : ℕ) : ZMod 293)) + 17))) = true
  have hcast : (i : ZMod 293) = ((i % 293 : ℕ) : ZMod 293) :=
    (ZMod.natCast_mod i 293).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 257 231358021807701134804540197275400065808365113467148439291186951745280929693695) (.leaf 263 14691120880271870432578865164240856359125270499464608419148410077277842015518207)) (.node (.leaf 269 948566977829834228242574032216064942829482460889802769267893618039833870706146303) (.leaf 271 3794275180128377091639574036761691478339887928951830933296806959309512658856574943))) (.node (.node (.leaf 277 209570712451653786824355420371829050542966849305328221352663571009991719434858790911) (.leaf 281 3885337755499833120890522110100353550143810700370339100409353039196560543627715018743)) (.node (.leaf 283 15298517526277616433382158763494365299079639103769163866072778674517223287256990612479) (.leaf 293 15898316546752310228922859257391317550145303335935861122357080606739715736369045918711287))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group3TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group3Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_257 i
          have hA := even22_allowed_int even22A257 even22_allowed_257 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_263 i
          have hA := even22_allowed_int even22A263 even22_allowed_263 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_269 i
          have hA := even22_allowed_int even22A269 even22_allowed_269 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_271 i
          have hA := even22_allowed_int even22A271 even22_allowed_271 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_277 i
          have hA := even22_allowed_int even22A277 even22_allowed_277 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_281 i
          have hA := even22_allowed_int even22A281 even22_allowed_281 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_283 i
          have hA := even22_allowed_int even22A283 even22_allowed_283 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_293 i
          have hA := even22_allowed_int even22A293 even22_allowed_293 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
