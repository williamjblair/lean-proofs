import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (16000000 + (r.val : ZMod 307)) + 21))) = true →
      (259085505340361511405219953443566711635537659535042760037891230508908093417346849956121345978).testBit r.val = true := by decide

theorem even22_b21_s1_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (16000000 + (i : ZMod 307)) + 21))) = true) :
    (259085505340361511405219953443566711635537659535042760037891230508908093417346849956121345978).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_307_fin r
  change even22A307
    (-(33 * (46 * (16000000 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (16000000 + (r.val : ZMod 311)) + 21))) = true →
      (4155044132665661527653682474762580325401196765924866845830648212335680768897238939621437439999).testBit r.val = true := by decide

theorem even22_b21_s1_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (16000000 + (i : ZMod 311)) + 21))) = true) :
    (4155044132665661527653682474762580325401196765924866845830648212335680768897238939621437439999).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_311_fin r
  change even22A311
    (-(33 * (46 * (16000000 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (16000000 + (r.val : ZMod 313)) + 21))) = true →
      (16589620991268054682951277179233663336068454414433035244718319306082220781263711490360892977150).testBit r.val = true := by decide

theorem even22_b21_s1_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (16000000 + (i : ZMod 313)) + 21))) = true) :
    (16589620991268054682951277179233663336068454414433035244718319306082220781263711490360892977150).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_313_fin r
  change even22A313
    (-(33 * (46 * (16000000 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (16000000 + (r.val : ZMod 317)) + 21))) = true →
      (200167303173674148841015299597501756463005048904700937595265508095475318023459696762810580072901).testBit r.val = true := by decide

theorem even22_b21_s1_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (16000000 + (i : ZMod 317)) + 21))) = true) :
    (200167303173674148841015299597501756463005048904700937595265508095475318023459696762810580072901).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_317_fin r
  change even22A317
    (-(33 * (46 * (16000000 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (16000000 + (r.val : ZMod 331)) + 21))) = true →
      (4096817920084206121749261737159085351128827652599148401155717927261296018629732002159319845523811326).testBit r.val = true := by decide

theorem even22_b21_s1_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (16000000 + (i : ZMod 331)) + 21))) = true) :
    (4096817920084206121749261737159085351128827652599148401155717927261296018629732002159319845523811326).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_331_fin r
  change even22A331
    (-(33 * (46 * (16000000 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (16000000 + (r.val : ZMod 337)) + 21))) = true →
      (279830285613886810058152761195947700390947114229381135093370366887296860504217920830020801832312241660).testBit r.val = true := by decide

theorem even22_b21_s1_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (16000000 + (i : ZMod 337)) + 21))) = true) :
    (279830285613886810058152761195947700390947114229381135093370366887296860504217920830020801832312241660).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_337_fin r
  change even22A337
    (-(33 * (46 * (16000000 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (16000000 + (r.val : ZMod 347)) + 21))) = true →
      (268768822248639013226093656818056426339259128512698760200313171504236049770022904662632549166690793947135).testBit r.val = true := by decide

theorem even22_b21_s1_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (16000000 + (i : ZMod 347)) + 21))) = true) :
    (268768822248639013226093656818056426339259128512698760200313171504236049770022904662632549166690793947135).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_347_fin r
  change even22A347
    (-(33 * (46 * (16000000 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (16000000 + (r.val : ZMod 349)) + 21))) = true →
      (1128826975551924668315744728755905470463634935996668147144888704666744903982611851939512386139984841654271).testBit r.val = true := by decide

theorem even22_b21_s1_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (16000000 + (i : ZMod 349)) + 21))) = true) :
    (1128826975551924668315744728755905470463634935996668147144888704666744903982611851939512386139984841654271).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_349_fin r
  change even22A349
    (-(33 * (46 * (16000000 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 259085505340361511405219953443566711635537659535042760037891230508908093417346849956121345978) (.leaf 311 4155044132665661527653682474762580325401196765924866845830648212335680768897238939621437439999)) (.node (.leaf 313 16589620991268054682951277179233663336068454414433035244718319306082220781263711490360892977150) (.leaf 317 200167303173674148841015299597501756463005048904700937595265508095475318023459696762810580072901))) (.node (.node (.leaf 331 4096817920084206121749261737159085351128827652599148401155717927261296018629732002159319845523811326) (.leaf 337 279830285613886810058152761195947700390947114229381135093370366887296860504217920830020801832312241660)) (.node (.leaf 347 268768822248639013226093656818056426339259128512698760200313171504236049770022904662632549166690793947135) (.leaf 349 1128826975551924668315744728755905470463634935996668147144888704666744903982611851939512386139984841654271))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
