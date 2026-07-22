import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s0_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (0 + (r.val : ZMod 307)) + 21))) = true →
      (260740535030932408971459236833326331462050469512122522389185133686287074077110353488850714557).testBit r.val = true := by decide

theorem even22_b21_s0_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (0 + (i : ZMod 307)) + 21))) = true) :
    (260740535030932408971459236833326331462050469512122522389185133686287074077110353488850714557).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_307_fin r
  change even22A307
    (-(33 * (46 * (0 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (0 + (r.val : ZMod 311)) + 21))) = true →
      (3128887131433623263960778377458640336437765778213295203088657505298143350660323848951523426295).testBit r.val = true := by decide

theorem even22_b21_s0_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (0 + (i : ZMod 311)) + 21))) = true) :
    (3128887131433623263960778377458640336437765778213295203088657505298143350660323848951523426295).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_311_fin r
  change even22A311
    (-(33 * (46 * (0 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (0 + (r.val : ZMod 313)) + 21))) = true →
      (16654805645187519051394409152527196379264543740035158678009460146558212857688781229521576656879).testBit r.val = true := by decide

theorem even22_b21_s0_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (0 + (i : ZMod 313)) + 21))) = true) :
    (16654805645187519051394409152527196379264543740035158678009460146558212857688781229521576656879).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_313_fin r
  change even22A313
    (-(33 * (46 * (0 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (0 + (r.val : ZMod 317)) + 21))) = true →
      (133499189743068679434222939805347337372941338722009791425263850510798018833267337729732528567950).testBit r.val = true := by decide

theorem even22_b21_s0_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (0 + (i : ZMod 317)) + 21))) = true) :
    (133499189743068679434222939805347337372941338722009791425263850510798018833267337729732528567950).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_317_fin r
  change even22A317
    (-(33 * (46 * (0 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (0 + (r.val : ZMod 331)) + 21))) = true →
      (3073601239419489812163337808156472061142629246235730579491389332431723741070410008940584426394351081).testBit r.val = true := by decide

theorem even22_b21_s0_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (0 + (i : ZMod 331)) + 21))) = true) :
    (3073601239419489812163337808156472061142629246235730579491389332431723741070410008940584426394351081).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_331_fin r
  change even22A331
    (-(33 * (46 * (0 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (0 + (r.val : ZMod 337)) + 21))) = true →
      (139979772326004650077438834045229022859178133269808149589211276220055343679801218240366429960807370555).testBit r.val = true := by decide

theorem even22_b21_s0_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (0 + (i : ZMod 337)) + 21))) = true) :
    (139979772326004650077438834045229022859178133269808149589211276220055343679801218240366429960807370555).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_337_fin r
  change even22A337
    (-(33 * (46 * (0 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (0 + (r.val : ZMod 347)) + 21))) = true →
      (286687326932009311869373464450930816099297407584426961003604610846685445187676030477799377417796574969855).testBit r.val = true := by decide

theorem even22_b21_s0_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (0 + (i : ZMod 347)) + 21))) = true) :
    (286687326932009311869373464450930816099297407584426961003604610846685445187676030477799377417796574969855).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_347_fin r
  change even22A347
    (-(33 * (46 * (0 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (0 + (r.val : ZMod 349)) + 21))) = true →
      (1146346512103619532130650995354895737887648750168596471760671387573431213531856551053220959041746072109055).testBit r.val = true := by decide

theorem even22_b21_s0_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (0 + (i : ZMod 349)) + 21))) = true) :
    (1146346512103619532130650995354895737887648750168596471760671387573431213531856551053220959041746072109055).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_349_fin r
  change even22A349
    (-(33 * (46 * (0 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S0Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260740535030932408971459236833326331462050469512122522389185133686287074077110353488850714557) (.leaf 311 3128887131433623263960778377458640336437765778213295203088657505298143350660323848951523426295)) (.node (.leaf 313 16654805645187519051394409152527196379264543740035158678009460146558212857688781229521576656879) (.leaf 317 133499189743068679434222939805347337372941338722009791425263850510798018833267337729732528567950))) (.node (.node (.leaf 331 3073601239419489812163337808156472061142629246235730579491389332431723741070410008940584426394351081) (.leaf 337 139979772326004650077438834045229022859178133269808149589211276220055343679801218240366429960807370555)) (.node (.leaf 347 286687326932009311869373464450930816099297407584426961003604610846685445187676030477799377417796574969855) (.leaf 349 1146346512103619532130650995354895737887648750168596471760671387573431213531856551053220959041746072109055))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S0Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S0Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
