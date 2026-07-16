import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_211_fin : ∀ r : Fin 211,
    even22A211 (-(33 * (46 * (16000000 + (r.val : ZMod 211)) + 21))) = true →
      (3291009110811173231788404282750063513975968550819867534003535869).testBit r.val = true := by decide

theorem even22_b21_s1_map_211 (i : ℕ)
    (h : even22A211 (-(33 * (46 * (16000000 + (i : ZMod 211)) + 21))) = true) :
    (3291009110811173231788404282750063513975968550819867534003535869).testBit (i % 211) = true := by
  let r : Fin 211 := ⟨i % 211, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_211_fin r
  change even22A211
    (-(33 * (46 * (16000000 + ((i % 211 : ℕ) : ZMod 211)) + 21))) = true
  have hcast : (i : ZMod 211) = ((i % 211 : ℕ) : ZMod 211) :=
    (ZMod.natCast_mod i 211).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_223_fin : ∀ r : Fin 223,
    even22A223 (-(33 * (46 * (16000000 + (r.val : ZMod 223)) + 21))) = true →
      (12630776679856624335160351095803789284604122960161682292756770193407).testBit r.val = true := by decide

theorem even22_b21_s1_map_223 (i : ℕ)
    (h : even22A223 (-(33 * (46 * (16000000 + (i : ZMod 223)) + 21))) = true) :
    (12630776679856624335160351095803789284604122960161682292756770193407).testBit (i % 223) = true := by
  let r : Fin 223 := ⟨i % 223, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_223_fin r
  change even22A223
    (-(33 * (46 * (16000000 + ((i % 223 : ℕ) : ZMod 223)) + 21))) = true
  have hcast : (i : ZMod 223) = ((i % 223 : ℕ) : ZMod 223) :=
    (ZMod.natCast_mod i 223).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_227_fin : ∀ r : Fin 227,
    even22A227 (-(33 * (46 * (16000000 + (r.val : ZMod 227)) + 21))) = true →
      (215679573337202017354854045084992091849249625567924650678061077889019).testBit r.val = true := by decide

theorem even22_b21_s1_map_227 (i : ℕ)
    (h : even22A227 (-(33 * (46 * (16000000 + (i : ZMod 227)) + 21))) = true) :
    (215679573337202017354854045084992091849249625567924650678061077889019).testBit (i % 227) = true := by
  let r : Fin 227 := ⟨i % 227, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_227_fin r
  change even22A227
    (-(33 * (46 * (16000000 + ((i % 227 : ℕ) : ZMod 227)) + 21))) = true
  have hcast : (i : ZMod 227) = ((i % 227 : ℕ) : ZMod 227) :=
    (ZMod.natCast_mod i 227).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_229_fin : ∀ r : Fin 229,
    even22A229 (-(33 * (46 * (16000000 + (r.val : ZMod 229)) + 21))) = true →
      (862718293317410444823757224046710872598022688783537180232443500683007).testBit r.val = true := by decide

theorem even22_b21_s1_map_229 (i : ℕ)
    (h : even22A229 (-(33 * (46 * (16000000 + (i : ZMod 229)) + 21))) = true) :
    (862718293317410444823757224046710872598022688783537180232443500683007).testBit (i % 229) = true := by
  let r : Fin 229 := ⟨i % 229, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_229_fin r
  change even22A229
    (-(33 * (46 * (16000000 + ((i % 229 : ℕ) : ZMod 229)) + 21))) = true
  have hcast : (i : ZMod 229) = ((i % 229 : ℕ) : ZMod 229) :=
    (ZMod.natCast_mod i 229).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_233_fin : ∀ r : Fin 233,
    even22A233 (-(33 * (46 * (16000000 + (r.val : ZMod 233)) + 21))) = true →
      (13803491048076515083823998397585967446693652176399641296876699675262967).testBit r.val = true := by decide

theorem even22_b21_s1_map_233 (i : ℕ)
    (h : even22A233 (-(33 * (46 * (16000000 + (i : ZMod 233)) + 21))) = true) :
    (13803491048076515083823998397585967446693652176399641296876699675262967).testBit (i % 233) = true := by
  let r : Fin 233 := ⟨i % 233, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_233_fin r
  change even22A233
    (-(33 * (46 * (16000000 + ((i % 233 : ℕ) : ZMod 233)) + 21))) = true
  have hcast : (i : ZMod 233) = ((i % 233 : ℕ) : ZMod 233) :=
    (ZMod.natCast_mod i 233).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_239_fin : ∀ r : Fin 239,
    even22A239 (-(33 * (46 * (16000000 + (r.val : ZMod 239)) + 21))) = true →
      (883423532376229164686860288775048660253096713473987320014952133184978943).testBit r.val = true := by decide

theorem even22_b21_s1_map_239 (i : ℕ)
    (h : even22A239 (-(33 * (46 * (16000000 + (i : ZMod 239)) + 21))) = true) :
    (883423532376229164686860288775048660253096713473987320014952133184978943).testBit (i % 239) = true := by
  let r : Fin 239 := ⟨i % 239, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_239_fin r
  change even22A239
    (-(33 * (46 * (16000000 + ((i % 239 : ℕ) : ZMod 239)) + 21))) = true
  have hcast : (i : ZMod 239) = ((i % 239 : ℕ) : ZMod 239) :=
    (ZMod.natCast_mod i 239).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_241_fin : ∀ r : Fin 241,
    even22A241 (-(33 * (46 * (16000000 + (r.val : ZMod 241)) + 21))) = true →
      (3450872752145311750463133431117697278359738733739021964597456698945306623).testBit r.val = true := by decide

theorem even22_b21_s1_map_241 (i : ℕ)
    (h : even22A241 (-(33 * (46 * (16000000 + (i : ZMod 241)) + 21))) = true) :
    (3450872752145311750463133431117697278359738733739021964597456698945306623).testBit (i % 241) = true := by
  let r : Fin 241 := ⟨i % 241, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_241_fin r
  change even22A241
    (-(33 * (46 * (16000000 + ((i % 241 : ℕ) : ZMod 241)) + 21))) = true
  have hcast : (i : ZMod 241) = ((i % 241 : ℕ) : ZMod 241) :=
    (ZMod.natCast_mod i 241).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_251_fin : ∀ r : Fin 251,
    even22A251 (-(33 * (46 * (16000000 + (r.val : ZMod 251)) + 21))) = true →
      (3618502357303693222582198470946352644488861506254577435534216307871620005887).testBit r.val = true := by decide

theorem even22_b21_s1_map_251 (i : ℕ)
    (h : even22A251 (-(33 * (46 * (16000000 + (i : ZMod 251)) + 21))) = true) :
    (3618502357303693222582198470946352644488861506254577435534216307871620005887).testBit (i % 251) = true := by
  let r : Fin 251 := ⟨i % 251, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_251_fin r
  change even22A251
    (-(33 * (46 * (16000000 + ((i % 251 : ℕ) : ZMod 251)) + 21))) = true
  have hcast : (i : ZMod 251) = ((i % 251 : ℕ) : ZMod 251) :=
    (ZMod.natCast_mod i 251).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group2Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 211 3291009110811173231788404282750063513975968550819867534003535869) (.leaf 223 12630776679856624335160351095803789284604122960161682292756770193407)) (.node (.leaf 227 215679573337202017354854045084992091849249625567924650678061077889019) (.leaf 229 862718293317410444823757224046710872598022688783537180232443500683007))) (.node (.node (.leaf 233 13803491048076515083823998397585967446693652176399641296876699675262967) (.leaf 239 883423532376229164686860288775048660253096713473987320014952133184978943)) (.node (.leaf 241 3450872752145311750463133431117697278359738733739021964597456698945306623) (.leaf 251 3618502357303693222582198470946352644488861506254577435534216307871620005887))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group2TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group2Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_211 i
          have hA := even22_allowed_int even22A211 even22_allowed_211 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_223 i
          have hA := even22_allowed_int even22A223 even22_allowed_223 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_227 i
          have hA := even22_allowed_int even22A227 even22_allowed_227 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_229 i
          have hA := even22_allowed_int even22A229 even22_allowed_229 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_233 i
          have hA := even22_allowed_int even22A233 even22_allowed_233 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_239 i
          have hA := even22_allowed_int even22A239 even22_allowed_239 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_241 i
          have hA := even22_allowed_int even22A241 even22_allowed_241 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_251 i
          have hA := even22_allowed_int even22A251 even22_allowed_251 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
