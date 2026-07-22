import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s5_map_211_fin : ∀ r : Fin 211,
    even22A211 (-(33 * (46 * (80000000 + (r.val : ZMod 211)) + 17))) = true →
      (3289402176597217732986417512865532543286780215973463044166434815).testBit r.val = true := by decide

theorem even22_b17_s5_map_211 (i : ℕ)
    (h : even22A211 (-(33 * (46 * (80000000 + (i : ZMod 211)) + 17))) = true) :
    (3289402176597217732986417512865532543286780215973463044166434815).testBit (i % 211) = true := by
  let r : Fin 211 := ⟨i % 211, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_211_fin r
  change even22A211
    (-(33 * (46 * (80000000 + ((i % 211 : ℕ) : ZMod 211)) + 17))) = true
  have hcast : (i : ZMod 211) = ((i % 211 : ℕ) : ZMod 211) :=
    (ZMod.natCast_mod i 211).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_223_fin : ∀ r : Fin 223,
    even22A223 (-(33 * (46 * (80000000 + (r.val : ZMod 223)) + 17))) = true →
      (13479973333575319897333507542476984252646981571420855704645640650751).testBit r.val = true := by decide

theorem even22_b17_s5_map_223 (i : ℕ)
    (h : even22A223 (-(33 * (46 * (80000000 + (i : ZMod 223)) + 17))) = true) :
    (13479973333575319897333507542476984252646981571420855704645640650751).testBit (i % 223) = true := by
  let r : Fin 223 := ⟨i % 223, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_223_fin r
  change even22A223
    (-(33 * (46 * (80000000 + ((i % 223 : ℕ) : ZMod 223)) + 17))) = true
  have hcast : (i : ZMod 223) = ((i % 223 : ℕ) : ZMod 223) :=
    (ZMod.natCast_mod i 223).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_227_fin : ∀ r : Fin 227,
    even22A227 (-(33 * (46 * (80000000 + (r.val : ZMod 227)) + 17))) = true →
      (215679566909452941227836059069515588564145089097739722899553358184447).testBit r.val = true := by decide

theorem even22_b17_s5_map_227 (i : ℕ)
    (h : even22A227 (-(33 * (46 * (80000000 + (i : ZMod 227)) + 17))) = true) :
    (215679566909452941227836059069515588564145089097739722899553358184447).testBit (i % 227) = true := by
  let r : Fin 227 := ⟨i % 227, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_227_fin r
  change even22A227
    (-(33 * (46 * (80000000 + ((i % 227 : ℕ) : ZMod 227)) + 17))) = true
  have hcast : (i : ZMod 227) = ((i % 227 : ℕ) : ZMod 227) :=
    (ZMod.natCast_mod i 227).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_229_fin : ∀ r : Fin 229,
    even22A229 (-(33 * (46 * (80000000 + (r.val : ZMod 229)) + 17))) = true →
      (862191320514338357182650556702094941295805731533156756213081359515647).testBit r.val = true := by decide

theorem even22_b17_s5_map_229 (i : ℕ)
    (h : even22A229 (-(33 * (46 * (80000000 + (i : ZMod 229)) + 17))) = true) :
    (862191320514338357182650556702094941295805731533156756213081359515647).testBit (i % 229) = true := by
  let r : Fin 229 := ⟨i % 229, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_229_fin r
  change even22A229
    (-(33 * (46 * (80000000 + ((i % 229 : ℕ) : ZMod 229)) + 17))) = true
  have hcast : (i : ZMod 229) = ((i % 229 : ℕ) : ZMod 229) :=
    (ZMod.natCast_mod i 229).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_233_fin : ∀ r : Fin 233,
    even22A233 (-(33 * (46 * (80000000 + (r.val : ZMod 233)) + 17))) = true →
      (11862376533546281509653473793059360607464915078433258058707192762073087).testBit r.val = true := by decide

theorem even22_b17_s5_map_233 (i : ℕ)
    (h : even22A233 (-(33 * (46 * (80000000 + (i : ZMod 233)) + 17))) = true) :
    (11862376533546281509653473793059360607464915078433258058707192762073087).testBit (i % 233) = true := by
  let r : Fin 233 := ⟨i % 233, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_233_fin r
  change even22A233
    (-(33 * (46 * (80000000 + ((i % 233 : ℕ) : ZMod 233)) + 17))) = true
  have hcast : (i : ZMod 233) = ((i % 233 : ℕ) : ZMod 233) :=
    (ZMod.natCast_mod i 233).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_239_fin : ∀ r : Fin 239,
    even22A239 (-(33 * (46 * (80000000 + (r.val : ZMod 239)) + 17))) = true →
      (883423532337340164372494903985816867271161008582520842877399230800986111).testBit r.val = true := by decide

theorem even22_b17_s5_map_239 (i : ℕ)
    (h : even22A239 (-(33 * (46 * (80000000 + (i : ZMod 239)) + 17))) = true) :
    (883423532337340164372494903985816867271161008582520842877399230800986111).testBit (i % 239) = true := by
  let r : Fin 239 := ⟨i % 239, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_239_fin r
  change even22A239
    (-(33 * (46 * (80000000 + ((i % 239 : ℕ) : ZMod 239)) + 17))) = true
  have hcast : (i : ZMod 239) = ((i % 239 : ℕ) : ZMod 239) :=
    (ZMod.natCast_mod i 239).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_241_fin : ∀ r : Fin 241,
    even22A241 (-(33 * (46 * (80000000 + (r.val : ZMod 241)) + 17))) = true →
      (3202408619910941024352748720013278018474051553702374109660189588025507839).testBit r.val = true := by decide

theorem even22_b17_s5_map_241 (i : ℕ)
    (h : even22A241 (-(33 * (46 * (80000000 + (i : ZMod 241)) + 17))) = true) :
    (3202408619910941024352748720013278018474051553702374109660189588025507839).testBit (i % 241) = true := by
  let r : Fin 241 := ⟨i % 241, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_241_fin r
  change even22A241
    (-(33 * (46 * (80000000 + ((i % 241 : ℕ) : ZMod 241)) + 17))) = true
  have hcast : (i : ZMod 241) = ((i % 241 : ℕ) : ZMod 241) :=
    (ZMod.natCast_mod i 241).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_251_fin : ∀ r : Fin 251,
    even22A251 (-(33 * (46 * (80000000 + (r.val : ZMod 251)) + 17))) = true →
      (3618502787823626345493615947907092541360144392843168621954340841668426579967).testBit r.val = true := by decide

theorem even22_b17_s5_map_251 (i : ℕ)
    (h : even22A251 (-(33 * (46 * (80000000 + (i : ZMod 251)) + 17))) = true) :
    (3618502787823626345493615947907092541360144392843168621954340841668426579967).testBit (i % 251) = true := by
  let r : Fin 251 := ⟨i % 251, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_251_fin r
  change even22A251
    (-(33 * (46 * (80000000 + ((i % 251 : ℕ) : ZMod 251)) + 17))) = true
  have hcast : (i : ZMod 251) = ((i % 251 : ℕ) : ZMod 251) :=
    (ZMod.natCast_mod i 251).symm
  rw [← hcast]
  exact h

def even22PackedB17S5Group2Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 211 3289402176597217732986417512865532543286780215973463044166434815) (.leaf 223 13479973333575319897333507542476984252646981571420855704645640650751)) (.node (.leaf 227 215679566909452941227836059069515588564145089097739722899553358184447) (.leaf 229 862191320514338357182650556702094941295805731533156756213081359515647))) (.node (.node (.leaf 233 11862376533546281509653473793059360607464915078433258058707192762073087) (.leaf 239 883423532337340164372494903985816867271161008582520842877399230800986111)) (.node (.leaf 241 3202408619910941024352748720013278018474051553702374109660189588025507839) (.leaf 251 3618502787823626345493615947907092541360144392843168621954340841668426579967))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S5Group2TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S5Group2Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_211 i
          have hA := even22_allowed_int even22A211 even22_allowed_211 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_223 i
          have hA := even22_allowed_int even22A223 even22_allowed_223 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_227 i
          have hA := even22_allowed_int even22A227 even22_allowed_227 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_229 i
          have hA := even22_allowed_int even22A229 even22_allowed_229 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_233 i
          have hA := even22_allowed_int even22A233 even22_allowed_233 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_239 i
          have hA := even22_allowed_int even22A239 even22_allowed_239 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_241 i
          have hA := even22_allowed_int even22A241 even22_allowed_241 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_251 i
          have hA := even22_allowed_int even22A251 even22_allowed_251 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
