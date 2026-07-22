import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (48000000 + (r.val : ZMod 307)) + 25))) = true →
      (257938421631086969271435236039126997245028223699243061722220905357055446207084961258161430399).testBit r.val = true := by decide

theorem even22_b25_s3_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (48000000 + (i : ZMod 307)) + 25))) = true) :
    (257938421631086969271435236039126997245028223699243061722220905357055446207084961258161430399).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_307_fin r
  change even22A307
    (-(33 * (46 * (48000000 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (48000000 + (r.val : ZMod 311)) + 25))) = true →
      (4169812627954621435522807294418011677906481987139496384758928257188762505646589212259319020543).testBit r.val = true := by decide

theorem even22_b25_s3_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (48000000 + (i : ZMod 311)) + 25))) = true) :
    (4169812627954621435522807294418011677906481987139496384758928257188762505646589212259319020543).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_311_fin r
  change even22A311
    (-(33 * (46 * (48000000 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (48000000 + (r.val : ZMod 313)) + 25))) = true →
      (15122955088307224646553828675994224947090834417258317437324170480649158385300569389958418071535).testBit r.val = true := by decide

theorem even22_b25_s3_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (48000000 + (i : ZMod 313)) + 25))) = true) :
    (15122955088307224646553828675994224947090834417258317437324170480649158385300569389958418071535).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_313_fin r
  change even22A313
    (-(33 * (46 * (48000000 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (48000000 + (r.val : ZMod 317)) + 25))) = true →
      (233361750941409419590796303264573875826391264450736519818351219262363941944105448692648060644863).testBit r.val = true := by decide

theorem even22_b25_s3_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (48000000 + (i : ZMod 317)) + 25))) = true) :
    (233361750941409419590796303264573875826391264450736519818351219262363941944105448692648060644863).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_317_fin r
  change even22A317
    (-(33 * (46 * (48000000 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (48000000 + (r.val : ZMod 331)) + 25))) = true →
      (2167471848664428867141432486608608664745454803486535084055386901183555562107393974749092083731972063).testBit r.val = true := by decide

theorem even22_b25_s3_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (48000000 + (i : ZMod 331)) + 25))) = true) :
    (2167471848664428867141432486608608664745454803486535084055386901183555562107393974749092083731972063).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_331_fin r
  change even22A331
    (-(33 * (46 * (48000000 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (48000000 + (r.val : ZMod 337)) + 25))) = true →
      (244826831964200216862553031410296148786411701099336117574557334247494685102750476884486125643787796383).testBit r.val = true := by decide

theorem even22_b25_s3_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (48000000 + (i : ZMod 337)) + 25))) = true) :
    (244826831964200216862553031410296148786411701099336117574557334247494685102750476884486125643787796383).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_337_fin r
  change even22A337
    (-(33 * (46 * (48000000 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (48000000 + (r.val : ZMod 347)) + 25))) = true →
      (286547342948200976506701898272597786552957847848484039619705328400107817982379952542128312507838364647407).testBit r.val = true := by decide

theorem even22_b25_s3_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (48000000 + (i : ZMod 347)) + 25))) = true) :
    (286547342948200976506701898272597786552957847848484039619705328400107817982379952542128312507838364647407).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_347_fin r
  change even22A347
    (-(33 * (46 * (48000000 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (48000000 + (r.val : ZMod 349)) + 25))) = true →
      (1146679298883929853119903940936609337586037777558408247748779162994138326583064159690886241826878944833471).testBit r.val = true := by decide

theorem even22_b25_s3_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (48000000 + (i : ZMod 349)) + 25))) = true) :
    (1146679298883929853119903940936609337586037777558408247748779162994138326583064159690886241826878944833471).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_349_fin r
  change even22A349
    (-(33 * (46 * (48000000 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 257938421631086969271435236039126997245028223699243061722220905357055446207084961258161430399) (.leaf 311 4169812627954621435522807294418011677906481987139496384758928257188762505646589212259319020543)) (.node (.leaf 313 15122955088307224646553828675994224947090834417258317437324170480649158385300569389958418071535) (.leaf 317 233361750941409419590796303264573875826391264450736519818351219262363941944105448692648060644863))) (.node (.node (.leaf 331 2167471848664428867141432486608608664745454803486535084055386901183555562107393974749092083731972063) (.leaf 337 244826831964200216862553031410296148786411701099336117574557334247494685102750476884486125643787796383)) (.node (.leaf 347 286547342948200976506701898272597786552957847848484039619705328400107817982379952542128312507838364647407) (.leaf 349 1146679298883929853119903940936609337586037777558408247748779162994138326583064159690886241826878944833471))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
