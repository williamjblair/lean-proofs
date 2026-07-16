import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s2_map_83_fin : ∀ r : Fin 83,
    even22A83 (-(33 * (46 * (32000000 + (r.val : ZMod 83)) + 21))) = true →
      (9633627625054076168830975).testBit r.val = true := by decide

theorem even22_b21_s2_map_83 (i : ℕ)
    (h : even22A83 (-(33 * (46 * (32000000 + (i : ZMod 83)) + 21))) = true) :
    (9633627625054076168830975).testBit (i % 83) = true := by
  let r : Fin 83 := ⟨i % 83, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_83_fin r
  change even22A83
    (-(33 * (46 * (32000000 + ((i % 83 : ℕ) : ZMod 83)) + 21))) = true
  have hcast : (i : ZMod 83) = ((i % 83 : ℕ) : ZMod 83) :=
    (ZMod.natCast_mod i 83).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_97_fin : ∀ r : Fin 97,
    even22A97 (-(33 * (46 * (32000000 + (r.val : ZMod 97)) + 21))) = true →
      (158456249470664949272764350463).testBit r.val = true := by decide

theorem even22_b21_s2_map_97 (i : ℕ)
    (h : even22A97 (-(33 * (46 * (32000000 + (i : ZMod 97)) + 21))) = true) :
    (158456249470664949272764350463).testBit (i % 97) = true := by
  let r : Fin 97 := ⟨i % 97, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_97_fin r
  change even22A97
    (-(33 * (46 * (32000000 + ((i % 97 : ℕ) : ZMod 97)) + 21))) = true
  have hcast : (i : ZMod 97) = ((i % 97 : ℕ) : ZMod 97) :=
    (ZMod.natCast_mod i 97).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_101_fin : ∀ r : Fin 101,
    even22A101 (-(33 * (46 * (32000000 + (r.val : ZMod 101)) + 21))) = true →
      (2535301199866162992359822852095).testBit r.val = true := by decide

theorem even22_b21_s2_map_101 (i : ℕ)
    (h : even22A101 (-(33 * (46 * (32000000 + (i : ZMod 101)) + 21))) = true) :
    (2535301199866162992359822852095).testBit (i % 101) = true := by
  let r : Fin 101 := ⟨i % 101, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_101_fin r
  change even22A101
    (-(33 * (46 * (32000000 + ((i % 101 : ℕ) : ZMod 101)) + 21))) = true
  have hcast : (i : ZMod 101) = ((i % 101 : ℕ) : ZMod 101) :=
    (ZMod.natCast_mod i 101).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_127_fin : ∀ r : Fin 127,
    even22A127 (-(33 * (46 * (32000000 + (r.val : ZMod 127)) + 21))) = true →
      (159330659141721606912040078236796846079).testBit r.val = true := by decide

theorem even22_b21_s2_map_127 (i : ℕ)
    (h : even22A127 (-(33 * (46 * (32000000 + (i : ZMod 127)) + 21))) = true) :
    (159330659141721606912040078236796846079).testBit (i % 127) = true := by
  let r : Fin 127 := ⟨i % 127, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_127_fin r
  change even22A127
    (-(33 * (46 * (32000000 + ((i % 127 : ℕ) : ZMod 127)) + 21))) = true
  have hcast : (i : ZMod 127) = ((i % 127 : ℕ) : ZMod 127) :=
    (ZMod.natCast_mod i 127).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_131_fin : ∀ r : Fin 131,
    even22A131 (-(33 * (46 * (32000000 + (r.val : ZMod 131)) + 21))) = true →
      (2679702870314956260463560348315026178047).testBit r.val = true := by decide

theorem even22_b21_s2_map_131 (i : ℕ)
    (h : even22A131 (-(33 * (46 * (32000000 + (i : ZMod 131)) + 21))) = true) :
    (2679702870314956260463560348315026178047).testBit (i % 131) = true := by
  let r : Fin 131 := ⟨i % 131, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_131_fin r
  change even22A131
    (-(33 * (46 * (32000000 + ((i % 131 : ℕ) : ZMod 131)) + 21))) = true
  have hcast : (i : ZMod 131) = ((i % 131 : ℕ) : ZMod 131) :=
    (ZMod.natCast_mod i 131).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_139_fin : ∀ r : Fin 139,
    even22A139 (-(33 * (46 * (32000000 + (r.val : ZMod 139)) + 21))) = true →
      (696898286764479891905702301635013729320895).testBit r.val = true := by decide

theorem even22_b21_s2_map_139 (i : ℕ)
    (h : even22A139 (-(33 * (46 * (32000000 + (i : ZMod 139)) + 21))) = true) :
    (696898286764479891905702301635013729320895).testBit (i % 139) = true := by
  let r : Fin 139 := ⟨i % 139, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_139_fin r
  change even22A139
    (-(33 * (46 * (32000000 + ((i % 139 : ℕ) : ZMod 139)) + 21))) = true
  have hcast : (i : ZMod 139) = ((i % 139 : ℕ) : ZMod 139) :=
    (ZMod.natCast_mod i 139).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_149_fin : ∀ r : Fin 149,
    even22A149 (-(33 * (46 * (32000000 + (r.val : ZMod 149)) + 21))) = true →
      (713623846352939375700264272521139081321644031).testBit r.val = true := by decide

theorem even22_b21_s2_map_149 (i : ℕ)
    (h : even22A149 (-(33 * (46 * (32000000 + (i : ZMod 149)) + 21))) = true) :
    (713623846352939375700264272521139081321644031).testBit (i % 149) = true := by
  let r : Fin 149 := ⟨i % 149, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_149_fin r
  change even22A149
    (-(33 * (46 * (32000000 + ((i % 149 : ℕ) : ZMod 149)) + 21))) = true
  have hcast : (i : ZMod 149) = ((i % 149 : ℕ) : ZMod 149) :=
    (ZMod.natCast_mod i 149).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_151_fin : ∀ r : Fin 151,
    even22A151 (-(33 * (46 * (32000000 + (r.val : ZMod 151)) + 21))) = true →
      (2854495384072307172614586410702093422673526783).testBit r.val = true := by decide

theorem even22_b21_s2_map_151 (i : ℕ)
    (h : even22A151 (-(33 * (46 * (32000000 + (i : ZMod 151)) + 21))) = true) :
    (2854495384072307172614586410702093422673526783).testBit (i % 151) = true := by
  let r : Fin 151 := ⟨i % 151, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_151_fin r
  change even22A151
    (-(33 * (46 * (32000000 + ((i % 151 : ℕ) : ZMod 151)) + 21))) = true
  have hcast : (i : ZMod 151) = ((i % 151 : ℕ) : ZMod 151) :=
    (ZMod.natCast_mod i 151).symm
  rw [← hcast]
  exact h

def even22PackedB21S2Group0Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 83 9633627625054076168830975) (.leaf 97 158456249470664949272764350463)) (.node (.leaf 101 2535301199866162992359822852095) (.leaf 127 159330659141721606912040078236796846079))) (.node (.node (.leaf 131 2679702870314956260463560348315026178047) (.leaf 139 696898286764479891905702301635013729320895)) (.node (.leaf 149 713623846352939375700264272521139081321644031) (.leaf 151 2854495384072307172614586410702093422673526783))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S2Group0TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S2Group0Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_83 i
          have hA := even22_allowed_int even22A83 even22_allowed_83 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_97 i
          have hA := even22_allowed_int even22A97 even22_allowed_97 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_101 i
          have hA := even22_allowed_int even22A101 even22_allowed_101 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_127 i
          have hA := even22_allowed_int even22A127 even22_allowed_127 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_131 i
          have hA := even22_allowed_int even22A131 even22_allowed_131 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_139 i
          have hA := even22_allowed_int even22A139 even22_allowed_139 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_149 i
          have hA := even22_allowed_int even22A149 even22_allowed_149 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_151 i
          have hA := even22_allowed_int even22A151 even22_allowed_151 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
