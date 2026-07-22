import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (32000000 + (r.val : ZMod 307)) + 25))) = true →
      (129542752670180755702609976721783355817768829767521380018945615254454046708673424978060672989).testBit r.val = true := by decide

theorem even22_b25_s2_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (32000000 + (i : ZMod 307)) + 25))) = true) :
    (129542752670180755702609976721783355817768829767521380018945615254454046708673424978060672989).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_307_fin r
  change even22A307
    (-(33 * (46 * (32000000 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (32000000 + (r.val : ZMod 311)) + 25))) = true →
      (4139257088370205555132037036114431707109764265085653039745269962306676645949450919963610578941).testBit r.val = true := by decide

theorem even22_b25_s2_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (32000000 + (i : ZMod 311)) + 25))) = true) :
    (4139257088370205555132037036114431707109764265085653039745269962306676645949450919963610578941).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_311_fin r
  change even22A311
    (-(33 * (46 * (32000000 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (32000000 + (r.val : ZMod 313)) + 25))) = true →
      (16165909551018654541643940248690753638228263626892292369982423928265031608101685216529356947199).testBit r.val = true := by decide

theorem even22_b25_s2_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (32000000 + (i : ZMod 313)) + 25))) = true) :
    (16165909551018654541643940248690753638228263626892292369982423928265031608101685216529356947199).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_313_fin r
  change even22A313
    (-(33 * (46 * (32000000 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (32000000 + (r.val : ZMod 317)) + 25))) = true →
      (266864917576750286670454189955696235804118548930772060173112016460671023702246895990478949318655).testBit r.val = true := by decide

theorem even22_b25_s2_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (32000000 + (i : ZMod 317)) + 25))) = true) :
    (266864917576750286670454189955696235804118548930772060173112016460671023702246895990478949318655).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_317_fin r
  change even22A317
    (-(33 * (46 * (32000000 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (32000000 + (r.val : ZMod 331)) + 25))) = true →
      (4374167635324256217838450468638657679928250450438250829721437569526367210695569251342649101748535295).testBit r.val = true := by decide

theorem even22_b25_s2_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (32000000 + (i : ZMod 331)) + 25))) = true) :
    (4374167635324256217838450468638657679928250450438250829721437569526367210695569251342649101748535295).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_331_fin r
  change even22A331
    (-(33 * (46 * (32000000 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (32000000 + (r.val : ZMod 337)) + 25))) = true →
      (69957571403471702514538190298986925097736778557345283773342591721824215126054480207505200458078060415).testBit r.val = true := by decide

theorem even22_b25_s2_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (32000000 + (i : ZMod 337)) + 25))) = true) :
    (69957571403471702514538190298986925097736778557345283773342591721824215126054480207505200458078060415).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_337_fin r
  change even22A337
    (-(33 * (46 * (32000000 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (32000000 + (r.val : ZMod 347)) + 25))) = true →
      (286687309910854405964690861684267683529627311874341197787136121293307292724610545084799238570666933354495).testBit r.val = true := by decide

theorem even22_b25_s2_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (32000000 + (i : ZMod 347)) + 25))) = true) :
    (286687309910854405964690861684267683529627311874341197787136121293307292724610545084799238570666933354495).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_347_fin r
  change even22A347
    (-(33 * (46 * (32000000 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (32000000 + (r.val : ZMod 349)) + 25))) = true →
      (1146747734573584911181680918540511643318162831520017342766809564099242569979740896796799165939776449639935).testBit r.val = true := by decide

theorem even22_b25_s2_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (32000000 + (i : ZMod 349)) + 25))) = true) :
    (1146747734573584911181680918540511643318162831520017342766809564099242569979740896796799165939776449639935).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_349_fin r
  change even22A349
    (-(33 * (46 * (32000000 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 129542752670180755702609976721783355817768829767521380018945615254454046708673424978060672989) (.leaf 311 4139257088370205555132037036114431707109764265085653039745269962306676645949450919963610578941)) (.node (.leaf 313 16165909551018654541643940248690753638228263626892292369982423928265031608101685216529356947199) (.leaf 317 266864917576750286670454189955696235804118548930772060173112016460671023702246895990478949318655))) (.node (.node (.leaf 331 4374167635324256217838450468638657679928250450438250829721437569526367210695569251342649101748535295) (.leaf 337 69957571403471702514538190298986925097736778557345283773342591721824215126054480207505200458078060415)) (.node (.leaf 347 286687309910854405964690861684267683529627311874341197787136121293307292724610545084799238570666933354495) (.leaf 349 1146747734573584911181680918540511643318162831520017342766809564099242569979740896796799165939776449639935))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
