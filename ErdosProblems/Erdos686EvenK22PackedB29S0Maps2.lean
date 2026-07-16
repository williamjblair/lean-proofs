import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_211_fin : ∀ r : Fin 211,
    even22A211 (-(33 * (46 * (0 + (r.val : ZMod 211)) + 29))) = true →
      (3291009114642412084309938364699317258806805440972807589668585466).testBit r.val = true := by decide

theorem even22_b29_s0_map_211 (i : ℕ)
    (h : even22A211 (-(33 * (46 * (0 + (i : ZMod 211)) + 29))) = true) :
    (3291009114642412084309938364699317258806805440972807589668585466).testBit (i % 211) = true := by
  let r : Fin 211 := ⟨i % 211, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_211_fin r
  change even22A211
    (-(33 * (46 * (0 + ((i % 211 : ℕ) : ZMod 211)) + 29))) = true
  have hcast : (i : ZMod 211) = ((i % 211 : ℕ) : ZMod 211) :=
    (ZMod.natCast_mod i 211).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_223_fin : ∀ r : Fin 223,
    even22A223 (-(33 * (46 * (0 + (r.val : ZMod 223)) + 29))) = true →
      (13479973333575319897333507543509815336818568541917165613790197168031).testBit r.val = true := by decide

theorem even22_b29_s0_map_223 (i : ℕ)
    (h : even22A223 (-(33 * (46 * (0 + (i : ZMod 223)) + 29))) = true) :
    (13479973333575319897333507543509815336818568541917165613790197168031).testBit (i % 223) = true := by
  let r : Fin 223 := ⟨i % 223, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_223_fin r
  change even22A223
    (-(33 * (46 * (0 + ((i % 223 : ℕ) : ZMod 223)) + 29))) = true
  have hcast : (i : ZMod 223) = ((i % 223 : ℕ) : ZMod 223) :=
    (ZMod.natCast_mod i 223).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_227_fin : ∀ r : Fin 227,
    even22A227 (-(33 * (46 * (0 + (r.val : ZMod 227)) + 29))) = true →
      (188402867042770146396631270766790782312824902116211244644129480638463).testBit r.val = true := by decide

theorem even22_b29_s0_map_227 (i : ℕ)
    (h : even22A227 (-(33 * (46 * (0 + (i : ZMod 227)) + 29))) = true) :
    (188402867042770146396631270766790782312824902116211244644129480638463).testBit (i % 227) = true := by
  let r : Fin 227 := ⟨i % 227, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_227_fin r
  change even22A227
    (-(33 * (46 * (0 + ((i % 227 : ℕ) : ZMod 227)) + 29))) = true
  have hcast : (i : ZMod 227) = ((i % 227 : ℕ) : ZMod 227) :=
    (ZMod.natCast_mod i 227).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_229_fin : ∀ r : Fin 229,
    even22A229 (-(33 * (46 * (0 + (r.val : ZMod 229)) + 29))) = true →
      (862718290034510757145162755852031707238301639183430579886502115639295).testBit r.val = true := by decide

theorem even22_b29_s0_map_229 (i : ℕ)
    (h : even22A229 (-(33 * (46 * (0 + (i : ZMod 229)) + 29))) = true) :
    (862718290034510757145162755852031707238301639183430579886502115639295).testBit (i % 229) = true := by
  let r : Fin 229 := ⟨i % 229, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_229_fin r
  change even22A229
    (-(33 * (46 * (0 + ((i % 229 : ℕ) : ZMod 229)) + 29))) = true
  have hcast : (i : ZMod 229) = ((i % 229 : ℕ) : ZMod 229) :=
    (ZMod.natCast_mod i 229).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_233_fin : ∀ r : Fin 233,
    even22A233 (-(33 * (46 * (0 + (r.val : ZMod 233)) + 29))) = true →
      (13803282068994651909523194430228940659215310316645074053095632461086687).testBit r.val = true := by decide

theorem even22_b29_s0_map_233 (i : ℕ)
    (h : even22A233 (-(33 * (46 * (0 + (i : ZMod 233)) + 29))) = true) :
    (13803282068994651909523194430228940659215310316645074053095632461086687).testBit (i % 233) = true := by
  let r : Fin 233 := ⟨i % 233, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_233_fin r
  change even22A233
    (-(33 * (46 * (0 + ((i % 233 : ℕ) : ZMod 233)) + 29))) = true
  have hcast : (i : ZMod 233) = ((i % 233 : ℕ) : ZMod 233) :=
    (ZMod.natCast_mod i 233).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_239_fin : ∀ r : Fin 239,
    even22A239 (-(33 * (46 * (0 + (r.val : ZMod 239)) + 29))) = true →
      (883423532382764412614612789267885958256823150858492584007367552479002623).testBit r.val = true := by decide

theorem even22_b29_s0_map_239 (i : ℕ)
    (h : even22A239 (-(33 * (46 * (0 + (i : ZMod 239)) + 29))) = true) :
    (883423532382764412614612789267885958256823150858492584007367552479002623).testBit (i % 239) = true := by
  let r : Fin 239 := ⟨i % 239, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_239_fin r
  change even22A239
    (-(33 * (46 * (0 + ((i % 239 : ℕ) : ZMod 239)) + 29))) = true
  have hcast : (i : ZMod 239) = ((i % 239 : ℕ) : ZMod 239) :=
    (ZMod.natCast_mod i 239).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_241_fin : ∀ r : Fin 241,
    even22A241 (-(33 * (46 * (0 + (r.val : ZMod 241)) + 29))) = true →
      (3531968689678986578356495203513950600261494236920665870149050462995611647).testBit r.val = true := by decide

theorem even22_b29_s0_map_241 (i : ℕ)
    (h : even22A241 (-(33 * (46 * (0 + (i : ZMod 241)) + 29))) = true) :
    (3531968689678986578356495203513950600261494236920665870149050462995611647).testBit (i % 241) = true := by
  let r : Fin 241 := ⟨i % 241, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_241_fin r
  change even22A241
    (-(33 * (46 * (0 + ((i % 241 : ℕ) : ZMod 241)) + 29))) = true
  have hcast : (i : ZMod 241) = ((i % 241 : ℕ) : ZMod 241) :=
    (ZMod.natCast_mod i 241).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_251_fin : ∀ r : Fin 251,
    even22A251 (-(33 * (46 * (0 + (r.val : ZMod 251)) + 29))) = true →
      (3618502788662840072762011338812065852527755213660806301997585794549711634367).testBit r.val = true := by decide

theorem even22_b29_s0_map_251 (i : ℕ)
    (h : even22A251 (-(33 * (46 * (0 + (i : ZMod 251)) + 29))) = true) :
    (3618502788662840072762011338812065852527755213660806301997585794549711634367).testBit (i % 251) = true := by
  let r : Fin 251 := ⟨i % 251, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_251_fin r
  change even22A251
    (-(33 * (46 * (0 + ((i % 251 : ℕ) : ZMod 251)) + 29))) = true
  have hcast : (i : ZMod 251) = ((i % 251 : ℕ) : ZMod 251) :=
    (ZMod.natCast_mod i 251).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group2Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 211 3291009114642412084309938364699317258806805440972807589668585466) (.leaf 223 13479973333575319897333507543509815336818568541917165613790197168031)) (.node (.leaf 227 188402867042770146396631270766790782312824902116211244644129480638463) (.leaf 229 862718290034510757145162755852031707238301639183430579886502115639295))) (.node (.node (.leaf 233 13803282068994651909523194430228940659215310316645074053095632461086687) (.leaf 239 883423532382764412614612789267885958256823150858492584007367552479002623)) (.node (.leaf 241 3531968689678986578356495203513950600261494236920665870149050462995611647) (.leaf 251 3618502788662840072762011338812065852527755213660806301997585794549711634367))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group2TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group2Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_211 i
          have hA := even22_allowed_int even22A211 even22_allowed_211 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_223 i
          have hA := even22_allowed_int even22A223 even22_allowed_223 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_227 i
          have hA := even22_allowed_int even22A227 even22_allowed_227 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_229 i
          have hA := even22_allowed_int even22A229 even22_allowed_229 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_233 i
          have hA := even22_allowed_int even22A233 even22_allowed_233 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_239 i
          have hA := even22_allowed_int even22A239 even22_allowed_239 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_241 i
          have hA := even22_allowed_int even22A241 even22_allowed_241 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_251 i
          have hA := even22_allowed_int even22A251 even22_allowed_251 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
