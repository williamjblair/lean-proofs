import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_157_fin : ∀ r : Fin 157,
    even22A157 (-(33 * (46 * (0 + (r.val : ZMod 157)) + 17))) = true →
      (181974080479561364335253034094489190557016391671).testBit r.val = true := by decide

theorem even22_b17_s0_map_157 (i : ℕ)
    (h : even22A157 (-(33 * (46 * (0 + (i : ZMod 157)) + 17))) = true) :
    (181974080479561364335253034094489190557016391671).testBit (i % 157) = true := by
  let r : Fin 157 := ⟨i % 157, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_157_fin r
  change even22A157
    (-(33 * (46 * (0 + ((i % 157 : ℕ) : ZMod 157)) + 17))) = true
  have hcast : (i : ZMod 157) = ((i % 157 : ℕ) : ZMod 157) :=
    (ZMod.natCast_mod i 157).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_167_fin : ∀ r : Fin 167,
    even22A167 (-(33 * (46 * (0 + (r.val : ZMod 167)) + 17))) = true →
      (187072209576994444062387902920441998664287993724927).testBit r.val = true := by decide

theorem even22_b17_s0_map_167 (i : ℕ)
    (h : even22A167 (-(33 * (46 * (0 + (i : ZMod 167)) + 17))) = true) :
    (187072209576994444062387902920441998664287993724927).testBit (i % 167) = true := by
  let r : Fin 167 := ⟨i % 167, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_167_fin r
  change even22A167
    (-(33 * (46 * (0 + ((i % 167 : ℕ) : ZMod 167)) + 17))) = true
  have hcast : (i : ZMod 167) = ((i % 167 : ℕ) : ZMod 167) :=
    (ZMod.natCast_mod i 167).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_173_fin : ∀ r : Fin 173,
    even22A173 (-(33 * (46 * (0 + (r.val : ZMod 173)) + 17))) = true →
      (10476043736387912117684012842224690457225590877454335).testBit r.val = true := by decide

theorem even22_b17_s0_map_173 (i : ℕ)
    (h : even22A173 (-(33 * (46 * (0 + (i : ZMod 173)) + 17))) = true) :
    (10476043736387912117684012842224690457225590877454335).testBit (i % 173) = true := by
  let r : Fin 173 := ⟨i % 173, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_173_fin r
  change even22A173
    (-(33 * (46 * (0 + ((i % 173 : ℕ) : ZMod 173)) + 17))) = true
  have hcast : (i : ZMod 173) = ((i % 173 : ℕ) : ZMod 173) :=
    (ZMod.natCast_mod i 173).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_179_fin : ∀ r : Fin 179,
    even22A179 (-(33 * (46 * (0 + (r.val : ZMod 179)) + 17))) = true →
      (766247770432944429173981216714201912541609772053430255).testBit r.val = true := by decide

theorem even22_b17_s0_map_179 (i : ℕ)
    (h : even22A179 (-(33 * (46 * (0 + (i : ZMod 179)) + 17))) = true) :
    (766247770432944429173981216714201912541609772053430255).testBit (i % 179) = true := by
  let r : Fin 179 := ⟨i % 179, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_179_fin r
  change even22A179
    (-(33 * (46 * (0 + ((i % 179 : ℕ) : ZMod 179)) + 17))) = true
  have hcast : (i : ZMod 179) = ((i % 179 : ℕ) : ZMod 179) :=
    (ZMod.natCast_mod i 179).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_191_fin : ∀ r : Fin 191,
    even22A191 (-(33 * (46 * (0 + (r.val : ZMod 191)) + 17))) = true →
      (3135485876611608604201178017549513246870826409920854753279).testBit r.val = true := by decide

theorem even22_b17_s0_map_191 (i : ℕ)
    (h : even22A191 (-(33 * (46 * (0 + (i : ZMod 191)) + 17))) = true) :
    (3135485876611608604201178017549513246870826409920854753279).testBit (i % 191) = true := by
  let r : Fin 191 := ⟨i % 191, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_191_fin r
  change even22A191
    (-(33 * (46 * (0 + ((i % 191 : ℕ) : ZMod 191)) + 17))) = true
  have hcast : (i : ZMod 191) = ((i % 191 : ℕ) : ZMod 191) :=
    (ZMod.natCast_mod i 191).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_193_fin : ∀ r : Fin 193,
    even22A193 (-(33 * (46 * (0 + (r.val : ZMod 193)) + 17))) = true →
      (12554203470773361527671578846415332832204706385328441655231).testBit r.val = true := by decide

theorem even22_b17_s0_map_193 (i : ℕ)
    (h : even22A193 (-(33 * (46 * (0 + (i : ZMod 193)) + 17))) = true) :
    (12554203470773361527671578846415332832204706385328441655231).testBit (i % 193) = true := by
  let r : Fin 193 := ⟨i % 193, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_193_fin r
  change even22A193
    (-(33 * (46 * (0 + ((i % 193 : ℕ) : ZMod 193)) + 17))) = true
  have hcast : (i : ZMod 193) = ((i % 193 : ℕ) : ZMod 193) :=
    (ZMod.natCast_mod i 193).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_197_fin : ∀ r : Fin 197,
    even22A197 (-(33 * (46 * (0 + (r.val : ZMod 197)) + 17))) = true →
      (200867255532373606036741138001795075721596271209890646556671).testBit r.val = true := by decide

theorem even22_b17_s0_map_197 (i : ℕ)
    (h : even22A197 (-(33 * (46 * (0 + (i : ZMod 197)) + 17))) = true) :
    (200867255532373606036741138001795075721596271209890646556671).testBit (i % 197) = true := by
  let r : Fin 197 := ⟨i % 197, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_197_fin r
  change even22A197
    (-(33 * (46 * (0 + ((i % 197 : ℕ) : ZMod 197)) + 17))) = true
  have hcast : (i : ZMod 197) = ((i % 197 : ℕ) : ZMod 197) :=
    (ZMod.natCast_mod i 197).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_199_fin : ∀ r : Fin 199,
    even22A199 (-(33 * (46 * (0 + (r.val : ZMod 199)) + 17))) = true →
      (803469022129495137760092010429111270430273509453579830689791).testBit r.val = true := by decide

theorem even22_b17_s0_map_199 (i : ℕ)
    (h : even22A199 (-(33 * (46 * (0 + (i : ZMod 199)) + 17))) = true) :
    (803469022129495137760092010429111270430273509453579830689791).testBit (i % 199) = true := by
  let r : Fin 199 := ⟨i % 199, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_199_fin r
  change even22A199
    (-(33 * (46 * (0 + ((i % 199 : ℕ) : ZMod 199)) + 17))) = true
  have hcast : (i : ZMod 199) = ((i % 199 : ℕ) : ZMod 199) :=
    (ZMod.natCast_mod i 199).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group1Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 157 181974080479561364335253034094489190557016391671) (.leaf 167 187072209576994444062387902920441998664287993724927)) (.node (.leaf 173 10476043736387912117684012842224690457225590877454335) (.leaf 179 766247770432944429173981216714201912541609772053430255))) (.node (.node (.leaf 191 3135485876611608604201178017549513246870826409920854753279) (.leaf 193 12554203470773361527671578846415332832204706385328441655231)) (.node (.leaf 197 200867255532373606036741138001795075721596271209890646556671) (.leaf 199 803469022129495137760092010429111270430273509453579830689791))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group1TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group1Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_157 i
          have hA := even22_allowed_int even22A157 even22_allowed_157 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_167 i
          have hA := even22_allowed_int even22A167 even22_allowed_167 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_173 i
          have hA := even22_allowed_int even22A173 even22_allowed_173 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_179 i
          have hA := even22_allowed_int even22A179 even22_allowed_179 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_191 i
          have hA := even22_allowed_int even22A191 even22_allowed_191 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_193 i
          have hA := even22_allowed_int even22A193 even22_allowed_193 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_197 i
          have hA := even22_allowed_int even22A197 even22_allowed_197 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_199 i
          have hA := even22_allowed_int even22A199 even22_allowed_199 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
