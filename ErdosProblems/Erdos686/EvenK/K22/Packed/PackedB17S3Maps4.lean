import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s3_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (48000000 + (r.val : ZMod 307)) + 17))) = true →
      (260478018300922653791706953710471365601256116277750476269733680835232252796820543440932567295).testBit r.val = true := by decide

theorem even22_b17_s3_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (48000000 + (i : ZMod 307)) + 17))) = true) :
    (260478018300922653791706953710471365601256116277750476269733680835232252796820543440932567295).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_307_fin r
  change even22A307
    (-(33 * (46 * (48000000 + ((i % 307 : ℕ) : ZMod 307)) + 17))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (48000000 + (r.val : ZMod 311)) + 17))) = true →
      (4041479361020601974588151970811935706658952083726019661526045873405319208008439858599588526078).testBit r.val = true := by decide

theorem even22_b17_s3_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (48000000 + (i : ZMod 311)) + 17))) = true) :
    (4041479361020601974588151970811935706658952083726019661526045873405319208008439858599588526078).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_311_fin r
  change even22A311
    (-(33 * (46 * (48000000 + ((i % 311 : ℕ) : ZMod 311)) + 17))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (48000000 + (r.val : ZMod 313)) + 17))) = true →
      (16687271387842000833324799031958934654811320060320264589798450050619056538031359776990122999807).testBit r.val = true := by decide

theorem even22_b17_s3_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (48000000 + (i : ZMod 313)) + 17))) = true) :
    (16687271387842000833324799031958934654811320060320264589798450050619056538031359776990122999807).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_313_fin r
  change even22A313
    (-(33 * (46 * (48000000 + ((i % 313 : ℕ) : ZMod 313)) + 17))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (48000000 + (r.val : ZMod 317)) + 17))) = true →
      (233623582053093412216475420789184282269826315193081465705149109376629307013513804583229309059047).testBit r.val = true := by decide

theorem even22_b17_s3_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (48000000 + (i : ZMod 317)) + 17))) = true) :
    (233623582053093412216475420789184282269826315193081465705149109376629307013513804583229309059047).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_317_fin r
  change even22A317
    (-(33 * (46 * (48000000 + ((i % 317 : ℕ) : ZMod 317)) + 17))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (48000000 + (r.val : ZMod 331)) + 17))) = true →
      (2135986995164025301924102305631832634111472258422817922164419622110855308800216200381645343120424959).testBit r.val = true := by decide

theorem even22_b17_s3_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (48000000 + (i : ZMod 331)) + 17))) = true) :
    (2135986995164025301924102305631832634111472258422817922164419622110855308800216200381645343120424959).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_331_fin r
  change even22A331
    (-(33 * (46 * (48000000 + ((i % 331 : ℕ) : ZMod 331)) + 17))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (48000000 + (r.val : ZMod 337)) + 17))) = true →
      (277779773996871628130210338038098338771754009787318664739020831447470070190593605052142041900896909055).testBit r.val = true := by decide

theorem even22_b17_s3_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (48000000 + (i : ZMod 337)) + 17))) = true) :
    (277779773996871628130210338038098338771754009787318664739020831447470070190593605052142041900896909055).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_337_fin r
  change even22A337
    (-(33 * (46 * (48000000 + ((i % 337 : ℕ) : ZMod 337)) + 17))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (48000000 + (r.val : ZMod 347)) + 17))) = true →
      (143343659227275027327485396270540996623929374744661987677737765747740767312057023164990090719874099707903).testBit r.val = true := by decide

theorem even22_b17_s3_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (48000000 + (i : ZMod 347)) + 17))) = true) :
    (143343659227275027327485396270540996623929374744661987677737765747740767312057023164990090719874099707903).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_347_fin r
  change even22A347
    (-(33 * (46 * (48000000 + ((i % 347 : ℕ) : ZMod 347)) + 17))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (48000000 + (r.val : ZMod 349)) + 17))) = true →
      (1001165897616969964482986345821970738739662272959779890796763633524592452894843307995275917378311451311611).testBit r.val = true := by decide

theorem even22_b17_s3_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (48000000 + (i : ZMod 349)) + 17))) = true) :
    (1001165897616969964482986345821970738739662272959779890796763633524592452894843307995275917378311451311611).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_349_fin r
  change even22A349
    (-(33 * (46 * (48000000 + ((i % 349 : ℕ) : ZMod 349)) + 17))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB17S3Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260478018300922653791706953710471365601256116277750476269733680835232252796820543440932567295) (.leaf 311 4041479361020601974588151970811935706658952083726019661526045873405319208008439858599588526078)) (.node (.leaf 313 16687271387842000833324799031958934654811320060320264589798450050619056538031359776990122999807) (.leaf 317 233623582053093412216475420789184282269826315193081465705149109376629307013513804583229309059047))) (.node (.node (.leaf 331 2135986995164025301924102305631832634111472258422817922164419622110855308800216200381645343120424959) (.leaf 337 277779773996871628130210338038098338771754009787318664739020831447470070190593605052142041900896909055)) (.node (.leaf 347 143343659227275027327485396270540996623929374744661987677737765747740767312057023164990090719874099707903) (.leaf 349 1001165897616969964482986345821970738739662272959779890796763633524592452894843307995275917378311451311611))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S3Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S3Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
