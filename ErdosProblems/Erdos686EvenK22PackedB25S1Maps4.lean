import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s1_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (16000000 + (r.val : ZMod 307)) + 25))) = true →
      (260740570000873314006910142474863368038319211950681181235305555601823940223408725940162789342).testBit r.val = true := by decide

theorem even22_b25_s1_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (16000000 + (i : ZMod 307)) + 25))) = true) :
    (260740570000873314006910142474863368038319211950681181235305555601823940223408725940162789342).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_307_fin r
  change even22A307
    (-(33 * (46 * (16000000 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (16000000 + (r.val : ZMod 311)) + 25))) = true →
      (4171785773497030275086720699204497288136123407484111871697681338695752892744325136688808189947).testBit r.val = true := by decide

theorem even22_b25_s1_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (16000000 + (i : ZMod 311)) + 25))) = true) :
    (4171785773497030275086720699204497288136123407484111871697681338695752892744325136688808189947).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_311_fin r
  change even22A311
    (-(33 * (46 * (16000000 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (16000000 + (r.val : ZMod 313)) + 25))) = true →
      (6254718965331245194804022102252144819189453877969151117687841375198574469474916616127846875055).testBit r.val = true := by decide

theorem even22_b25_s1_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (16000000 + (i : ZMod 313)) + 25))) = true) :
    (6254718965331245194804022102252144819189453877969151117687841375198574469474916616127846875055).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_313_fin r
  change even22A313
    (-(33 * (46 * (16000000 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (16000000 + (r.val : ZMod 317)) + 25))) = true →
      (133493046808440745743985056465260292736556034042213844750222148374864505902694709871664624025595).testBit r.val = true := by decide

theorem even22_b25_s1_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (16000000 + (i : ZMod 317)) + 25))) = true) :
    (133493046808440745743985056465260292736556034042213844750222148374864505902694709871664624025595).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_317_fin r
  change even22A317
    (-(33 * (46 * (16000000 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (16000000 + (r.val : ZMod 331)) + 25))) = true →
      (4271440075082712692454687110985378616633382502230575011966898177785985401782017033063704878752161791).testBit r.val = true := by decide

theorem even22_b25_s1_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (16000000 + (i : ZMod 331)) + 25))) = true) :
    (4271440075082712692454687110985378616633382502230575011966898177785985401782017033063704878752161791).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_331_fin r
  change even22A331
    (-(33 * (46 * (16000000 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (16000000 + (r.val : ZMod 337)) + 25))) = true →
      (244971012660670307259119922314598906788698798683200431294176797270369323843090393189548872484415009742).testBit r.val = true := by decide

theorem even22_b25_s1_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (16000000 + (i : ZMod 337)) + 25))) = true) :
    (244971012660670307259119922314598906788698798683200431294176797270369323843090393189548872484415009742).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_337_fin r
  change even22A337
    (-(33 * (46 * (16000000 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (16000000 + (r.val : ZMod 347)) + 25))) = true →
      (268769368527339746036061265971886493633135321559494231988059209946400043839937597280879470380065400813567).testBit r.val = true := by decide

theorem even22_b25_s1_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (16000000 + (i : ZMod 347)) + 25))) = true) :
    (268769368527339746036061265971886493633135321559494231988059209946400043839937597280879470380065400813567).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_347_fin r
  change even22A347
    (-(33 * (46 * (16000000 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s1_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (16000000 + (r.val : ZMod 349)) + 25))) = true →
      (1146464961128318283888426446932658247809003149054335173478242457045460505938682357481287874426079706349047).testBit r.val = true := by decide

theorem even22_b25_s1_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (16000000 + (i : ZMod 349)) + 25))) = true) :
    (1146464961128318283888426446932658247809003149054335173478242457045460505938682357481287874426079706349047).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s1_map_349_fin r
  change even22A349
    (-(33 * (46 * (16000000 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S1Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260740570000873314006910142474863368038319211950681181235305555601823940223408725940162789342) (.leaf 311 4171785773497030275086720699204497288136123407484111871697681338695752892744325136688808189947)) (.node (.leaf 313 6254718965331245194804022102252144819189453877969151117687841375198574469474916616127846875055) (.leaf 317 133493046808440745743985056465260292736556034042213844750222148374864505902694709871664624025595))) (.node (.node (.leaf 331 4271440075082712692454687110985378616633382502230575011966898177785985401782017033063704878752161791) (.leaf 337 244971012660670307259119922314598906788698798683200431294176797270369323843090393189548872484415009742)) (.node (.leaf 347 268769368527339746036061265971886493633135321559494231988059209946400043839937597280879470380065400813567) (.leaf 349 1146464961128318283888426446932658247809003149054335173478242457045460505938682357481287874426079706349047))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S1Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S1Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s1_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
