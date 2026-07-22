import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s4_map_157_fin : ∀ r : Fin 157,
    even22A157 (-(33 * (46 * (64000000 + (r.val : ZMod 157)) + 25))) = true →
      (170907161765411847368224537388411748155454901759).testBit r.val = true := by decide

theorem even22_b25_s4_map_157 (i : ℕ)
    (h : even22A157 (-(33 * (46 * (64000000 + (i : ZMod 157)) + 25))) = true) :
    (170907161765411847368224537388411748155454901759).testBit (i % 157) = true := by
  let r : Fin 157 := ⟨i % 157, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_157_fin r
  change even22A157
    (-(33 * (46 * (64000000 + ((i % 157 : ℕ) : ZMod 157)) + 25))) = true
  have hcast : (i : ZMod 157) = ((i % 157 : ℕ) : ZMod 157) :=
    (ZMod.natCast_mod i 157).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_167_fin : ∀ r : Fin 167,
    even22A167 (-(33 * (46 * (64000000 + (r.val : ZMod 167)) + 25))) = true →
      (186889521873689210421907282739774573993541320572927).testBit r.val = true := by decide

theorem even22_b25_s4_map_167 (i : ℕ)
    (h : even22A167 (-(33 * (46 * (64000000 + (i : ZMod 167)) + 25))) = true) :
    (186889521873689210421907282739774573993541320572927).testBit (i % 167) = true := by
  let r : Fin 167 := ⟨i % 167, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_167_fin r
  change even22A167
    (-(33 * (46 * (64000000 + ((i % 167 : ℕ) : ZMod 167)) + 25))) = true
  have hcast : (i : ZMod 167) = ((i % 167 : ℕ) : ZMod 167) :=
    (ZMod.natCast_mod i 167).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_173_fin : ∀ r : Fin 173,
    even22A173 (-(33 * (46 * (64000000 + (r.val : ZMod 173)) + 25))) = true →
      (11972621413014756703328437720344376682756151219060735).testBit r.val = true := by decide

theorem even22_b25_s4_map_173 (i : ℕ)
    (h : even22A173 (-(33 * (46 * (64000000 + (i : ZMod 173)) + 25))) = true) :
    (11972621413014756703328437720344376682756151219060735).testBit (i % 173) = true := by
  let r : Fin 173 := ⟨i % 173, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_173_fin r
  change even22A173
    (-(33 * (46 * (64000000 + ((i % 173 : ℕ) : ZMod 173)) + 25))) = true
  have hcast : (i : ZMod 173) = ((i % 173 : ℕ) : ZMod 173) :=
    (ZMod.natCast_mod i 173).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_179_fin : ∀ r : Fin 179,
    even22A179 (-(33 * (46 * (64000000 + (r.val : ZMod 179)) + 25))) = true →
      (766247747596981335249991450363252097382487297095630847).testBit r.val = true := by decide

theorem even22_b25_s4_map_179 (i : ℕ)
    (h : even22A179 (-(33 * (46 * (64000000 + (i : ZMod 179)) + 25))) = true) :
    (766247747596981335249991450363252097382487297095630847).testBit (i % 179) = true := by
  let r : Fin 179 := ⟨i % 179, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_179_fin r
  change even22A179
    (-(33 * (46 * (64000000 + ((i % 179 : ℕ) : ZMod 179)) + 25))) = true
  have hcast : (i : ZMod 179) = ((i % 179 : ℕ) : ZMod 179) :=
    (ZMod.natCast_mod i 179).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_191_fin : ∀ r : Fin 191,
    even22A191 (-(33 * (46 * (64000000 + (r.val : ZMod 191)) + 25))) = true →
      (3138550867693340381907260887637553881067947265749237628927).testBit r.val = true := by decide

theorem even22_b25_s4_map_191 (i : ℕ)
    (h : even22A191 (-(33 * (46 * (64000000 + (i : ZMod 191)) + 25))) = true) :
    (3138550867693340381907260887637553881067947265749237628927).testBit (i % 191) = true := by
  let r : Fin 191 := ⟨i % 191, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_191_fin r
  change even22A191
    (-(33 * (46 * (64000000 + ((i % 191 : ℕ) : ZMod 191)) + 25))) = true
  have hcast : (i : ZMod 191) = ((i % 191 : ℕ) : ZMod 191) :=
    (ZMod.natCast_mod i 191).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_193_fin : ∀ r : Fin 193,
    even22A193 (-(33 * (46 * (64000000 + (r.val : ZMod 193)) + 25))) = true →
      (12548073488609897972238145458306731595470235932404974878719).testBit r.val = true := by decide

theorem even22_b25_s4_map_193 (i : ℕ)
    (h : even22A193 (-(33 * (46 * (64000000 + (i : ZMod 193)) + 25))) = true) :
    (12548073488609897972238145458306731595470235932404974878719).testBit (i % 193) = true := by
  let r : Fin 193 := ⟨i % 193, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_193_fin r
  change even22A193
    (-(33 * (46 * (64000000 + ((i % 193 : ℕ) : ZMod 193)) + 25))) = true
  have hcast : (i : ZMod 193) = ((i % 193 : ℕ) : ZMod 193) :=
    (ZMod.natCast_mod i 193).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_197_fin : ∀ r : Fin 197,
    even22A197 (-(33 * (46 * (64000000 + (r.val : ZMod 197)) + 25))) = true →
      (200867249546061650687674202620471153537775225176842580262911).testBit r.val = true := by decide

theorem even22_b25_s4_map_197 (i : ℕ)
    (h : even22A197 (-(33 * (46 * (64000000 + (i : ZMod 197)) + 25))) = true) :
    (200867249546061650687674202620471153537775225176842580262911).testBit (i % 197) = true := by
  let r : Fin 197 := ⟨i % 197, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_197_fin r
  change even22A197
    (-(33 * (46 * (64000000 + ((i % 197 : ℕ) : ZMod 197)) + 25))) = true
  have hcast : (i : ZMod 197) = ((i % 197 : ℕ) : ZMod 197) :=
    (ZMod.natCast_mod i 197).symm
  rw [← hcast]
  exact h


theorem even22_b25_s4_map_199_fin : ∀ r : Fin 199,
    even22A199 (-(33 * (46 * (64000000 + (r.val : ZMod 199)) + 25))) = true →
      (803469022129495137770981045521544193944248043325084374401023).testBit r.val = true := by decide

theorem even22_b25_s4_map_199 (i : ℕ)
    (h : even22A199 (-(33 * (46 * (64000000 + (i : ZMod 199)) + 25))) = true) :
    (803469022129495137770981045521544193944248043325084374401023).testBit (i % 199) = true := by
  let r : Fin 199 := ⟨i % 199, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s4_map_199_fin r
  change even22A199
    (-(33 * (46 * (64000000 + ((i % 199 : ℕ) : ZMod 199)) + 25))) = true
  have hcast : (i : ZMod 199) = ((i % 199 : ℕ) : ZMod 199) :=
    (ZMod.natCast_mod i 199).symm
  rw [← hcast]
  exact h

def even22PackedB25S4Group1Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 157 170907161765411847368224537388411748155454901759) (.leaf 167 186889521873689210421907282739774573993541320572927)) (.node (.leaf 173 11972621413014756703328437720344376682756151219060735) (.leaf 179 766247747596981335249991450363252097382487297095630847))) (.node (.node (.leaf 191 3138550867693340381907260887637553881067947265749237628927) (.leaf 193 12548073488609897972238145458306731595470235932404974878719)) (.node (.leaf 197 200867249546061650687674202620471153537775225176842580262911) (.leaf 199 803469022129495137770981045521544193944248043325084374401023))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S4Group1TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S4Group1Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_157 i
          have hA := even22_allowed_int even22A157 even22_allowed_157 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_167 i
          have hA := even22_allowed_int even22A167 even22_allowed_167 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_173 i
          have hA := even22_allowed_int even22A173 even22_allowed_173 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_179 i
          have hA := even22_allowed_int even22A179 even22_allowed_179 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_191 i
          have hA := even22_allowed_int even22A191 even22_allowed_191 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_193 i
          have hA := even22_allowed_int even22A193 even22_allowed_193 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_197 i
          have hA := even22_allowed_int even22A197 even22_allowed_197 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s4_map_199 i
          have hA := even22_allowed_int even22A199 even22_allowed_199 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
