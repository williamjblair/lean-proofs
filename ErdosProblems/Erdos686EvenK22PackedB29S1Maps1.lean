import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s1_map_157_fin : ∀ r : Fin 157,
    even22A157 (-(33 * (46 * (16000000 + (r.val : ZMod 157)) + 29))) = true →
      (182503633683535505128472540547330320749155057463).testBit r.val = true := by decide

theorem even22_b29_s1_map_157 (i : ℕ)
    (h : even22A157 (-(33 * (46 * (16000000 + (i : ZMod 157)) + 29))) = true) :
    (182503633683535505128472540547330320749155057463).testBit (i % 157) = true := by
  let r : Fin 157 := ⟨i % 157, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_157_fin r
  change even22A157
    (-(33 * (46 * (16000000 + ((i % 157 : ℕ) : ZMod 157)) + 29))) = true
  have hcast : (i : ZMod 157) = ((i % 157 : ℕ) : ZMod 157) :=
    (ZMod.natCast_mod i 157).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_167_fin : ∀ r : Fin 167,
    even22A167 (-(33 * (46 * (16000000 + (r.val : ZMod 167)) + 29))) = true →
      (187072208881457286075989685405248297529958765428735).testBit r.val = true := by decide

theorem even22_b29_s1_map_167 (i : ℕ)
    (h : even22A167 (-(33 * (46 * (16000000 + (i : ZMod 167)) + 29))) = true) :
    (187072208881457286075989685405248297529958765428735).testBit (i % 167) = true := by
  let r : Fin 167 := ⟨i % 167, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_167_fin r
  change even22A167
    (-(33 * (46 * (16000000 + ((i % 167 : ℕ) : ZMod 167)) + 29))) = true
  have hcast : (i : ZMod 167) = ((i % 167 : ℕ) : ZMod 167) :=
    (ZMod.natCast_mod i 167).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_173_fin : ∀ r : Fin 173,
    even22A173 (-(33 * (46 * (16000000 + (r.val : ZMod 173)) + 29))) = true →
      (11925853360620167812542068233755943620777780375977983).testBit r.val = true := by decide

theorem even22_b29_s1_map_173 (i : ℕ)
    (h : even22A173 (-(33 * (46 * (16000000 + (i : ZMod 173)) + 29))) = true) :
    (11925853360620167812542068233755943620777780375977983).testBit (i % 173) = true := by
  let r : Fin 173 := ⟨i % 173, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_173_fin r
  change even22A173
    (-(33 * (46 * (16000000 + ((i % 173 : ℕ) : ZMod 173)) + 29))) = true
  have hcast : (i : ZMod 173) = ((i % 173 : ℕ) : ZMod 173) :=
    (ZMod.natCast_mod i 173).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_179_fin : ∀ r : Fin 179,
    even22A179 (-(33 * (46 * (16000000 + (r.val : ZMod 179)) + 29))) = true →
      (766246308931307098276255309271351855595429391557980159).testBit r.val = true := by decide

theorem even22_b29_s1_map_179 (i : ℕ)
    (h : even22A179 (-(33 * (46 * (16000000 + (i : ZMod 179)) + 29))) = true) :
    (766246308931307098276255309271351855595429391557980159).testBit (i % 179) = true := by
  let r : Fin 179 := ⟨i % 179, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_179_fin r
  change even22A179
    (-(33 * (46 * (16000000 + ((i % 179 : ℕ) : ZMod 179)) + 29))) = true
  have hcast : (i : ZMod 179) = ((i % 179 : ℕ) : ZMod 179) :=
    (ZMod.natCast_mod i 179).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_191_fin : ∀ r : Fin 191,
    even22A191 (-(33 * (46 * (16000000 + (r.val : ZMod 191)) + 29))) = true →
      (3138455086722036263864247314914635709264291743722293428223).testBit r.val = true := by decide

theorem even22_b29_s1_map_191 (i : ℕ)
    (h : even22A191 (-(33 * (46 * (16000000 + (i : ZMod 191)) + 29))) = true) :
    (3138455086722036263864247314914635709264291743722293428223).testBit (i % 191) = true := by
  let r : Fin 191 := ⟨i % 191, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_191_fin r
  change even22A191
    (-(33 * (46 * (16000000 + ((i % 191 : ℕ) : ZMod 191)) + 29))) = true
  have hcast : (i : ZMod 191) = ((i % 191 : ℕ) : ZMod 191) :=
    (ZMod.natCast_mod i 191).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_193_fin : ∀ r : Fin 193,
    even22A193 (-(33 * (46 * (16000000 + (r.val : ZMod 193)) + 29))) = true →
      (12554203470773361527671578846415332227741801081604891738111).testBit r.val = true := by decide

theorem even22_b29_s1_map_193 (i : ℕ)
    (h : even22A193 (-(33 * (46 * (16000000 + (i : ZMod 193)) + 29))) = true) :
    (12554203470773361527671578846415332227741801081604891738111).testBit (i % 193) = true := by
  let r : Fin 193 := ⟨i % 193, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_193_fin r
  change even22A193
    (-(33 * (46 * (16000000 + ((i % 193 : ℕ) : ZMod 193)) + 29))) = true
  have hcast : (i : ZMod 193) = ((i % 193 : ℕ) : ZMod 193) :=
    (ZMod.natCast_mod i 193).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_197_fin : ∀ r : Fin 197,
    even22A197 (-(33 * (46 * (16000000 + (r.val : ZMod 197)) + 29))) = true →
      (194590153796987103678739330895412370460137990626774683090943).testBit r.val = true := by decide

theorem even22_b29_s1_map_197 (i : ℕ)
    (h : even22A197 (-(33 * (46 * (16000000 + (i : ZMod 197)) + 29))) = true) :
    (194590153796987103678739330895412370460137990626774683090943).testBit (i % 197) = true := by
  let r : Fin 197 := ⟨i % 197, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_197_fin r
  change even22A197
    (-(33 * (46 * (16000000 + ((i % 197 : ℕ) : ZMod 197)) + 29))) = true
  have hcast : (i : ZMod 197) = ((i % 197 : ℕ) : ZMod 197) :=
    (ZMod.natCast_mod i 197).symm
  rw [← hcast]
  exact h


theorem even22_b29_s1_map_199_fin : ∀ r : Fin 199,
    even22A199 (-(33 * (46 * (16000000 + (r.val : ZMod 199)) + 29))) = true →
      (803468998184252311741467634321409002037511279476560778756095).testBit r.val = true := by decide

theorem even22_b29_s1_map_199 (i : ℕ)
    (h : even22A199 (-(33 * (46 * (16000000 + (i : ZMod 199)) + 29))) = true) :
    (803468998184252311741467634321409002037511279476560778756095).testBit (i % 199) = true := by
  let r : Fin 199 := ⟨i % 199, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s1_map_199_fin r
  change even22A199
    (-(33 * (46 * (16000000 + ((i % 199 : ℕ) : ZMod 199)) + 29))) = true
  have hcast : (i : ZMod 199) = ((i % 199 : ℕ) : ZMod 199) :=
    (ZMod.natCast_mod i 199).symm
  rw [← hcast]
  exact h

def even22PackedB29S1Group1Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 157 182503633683535505128472540547330320749155057463) (.leaf 167 187072208881457286075989685405248297529958765428735)) (.node (.leaf 173 11925853360620167812542068233755943620777780375977983) (.leaf 179 766246308931307098276255309271351855595429391557980159))) (.node (.node (.leaf 191 3138455086722036263864247314914635709264291743722293428223) (.leaf 193 12554203470773361527671578846415332227741801081604891738111)) (.node (.leaf 197 194590153796987103678739330895412370460137990626774683090943) (.leaf 199 803468998184252311741467634321409002037511279476560778756095))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S1Group1TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S1Group1Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_157 i
          have hA := even22_allowed_int even22A157 even22_allowed_157 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_167 i
          have hA := even22_allowed_int even22A167 even22_allowed_167 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_173 i
          have hA := even22_allowed_int even22A173 even22_allowed_173 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_179 i
          have hA := even22_allowed_int even22A179 even22_allowed_179 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_191 i
          have hA := even22_allowed_int even22A191 even22_allowed_191 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_193 i
          have hA := even22_allowed_int even22A193 even22_allowed_193 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_197 i
          have hA := even22_allowed_int even22A197 even22_allowed_197 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s1_map_199 i
          have hA := even22_allowed_int even22A199 even22_allowed_199 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
