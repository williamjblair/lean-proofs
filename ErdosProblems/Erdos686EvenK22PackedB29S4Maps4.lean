import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s4_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (64000000 + (r.val : ZMod 307)) + 29))) = true →
      (259339513300950594156898142077763700929808089044241450901823441437208126288396029824818147263).testBit r.val = true := by decide

theorem even22_b29_s4_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (64000000 + (i : ZMod 307)) + 29))) = true) :
    (259339513300950594156898142077763700929808089044241450901823441437208126288396029824818147263).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_307_fin r
  change even22A307
    (-(33 * (46 * (64000000 + ((i % 307 : ℕ) : ZMod 307)) + 29))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (64000000 + (r.val : ZMod 311)) + 29))) = true →
      (4171722364116706727952836270323938925372819093837903898693964234263290500302198295515419377661).testBit r.val = true := by decide

theorem even22_b29_s4_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (64000000 + (i : ZMod 311)) + 29))) = true) :
    (4171722364116706727952836270323938925372819093837903898693964234263290500302198295515419377661).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_311_fin r
  change even22A311
    (-(33 * (46 * (64000000 + ((i % 311 : ℕ) : ZMod 311)) + 29))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (64000000 + (r.val : ZMod 313)) + 29))) = true →
      (8343572044316822385636437787307669781647781816606431441549844435574131614708149008653841592319).testBit r.val = true := by decide

theorem even22_b29_s4_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (64000000 + (i : ZMod 313)) + 29))) = true) :
    (8343572044316822385636437787307669781647781816606431441549844435574131614708149008653841592319).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_313_fin r
  change even22A313
    (-(33 * (46 * (64000000 + ((i % 313 : ℕ) : ZMod 313)) + 29))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (64000000 + (r.val : ZMod 317)) + 29))) = true →
      (266672453714469074765305771847618997201344065029640557894301630426346340648678649545501798557462).testBit r.val = true := by decide

theorem even22_b29_s4_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (64000000 + (i : ZMod 317)) + 29))) = true) :
    (266672453714469074765305771847618997201344065029640557894301630426346340648678649545501798557462).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_317_fin r
  change even22A317
    (-(33 * (46 * (64000000 + ((i % 317 : ℕ) : ZMod 317)) + 29))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (64000000 + (r.val : ZMod 331)) + 29))) = true →
      (3279541095277067317754940150502837250164891098426446084345439514934247151909701251946581837075971823).testBit r.val = true := by decide

theorem even22_b29_s4_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (64000000 + (i : ZMod 331)) + 29))) = true) :
    (3279541095277067317754940150502837250164891098426446084345439514934247151909701251946581837075971823).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_331_fin r
  change even22A331
    (-(33 * (46 * (64000000 + ((i % 331 : ℕ) : ZMod 331)) + 29))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (64000000 + (r.val : ZMod 337)) + 29))) = true →
      (271182777570219198955398471655865688270507190640582423290513311777229159198827707850578796405160116199).testBit r.val = true := by decide

theorem even22_b29_s4_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (64000000 + (i : ZMod 337)) + 29))) = true) :
    (271182777570219198955398471655865688270507190640582423290513311777229159198827707850578796405160116199).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_337_fin r
  change even22A337
    (-(33 * (46 * (64000000 + ((i % 337 : ℕ) : ZMod 337)) + 29))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (64000000 + (r.val : ZMod 347)) + 29))) = true →
      (286682952495198494365944553418505745694082810092385814371202795628500262179846284476763693705478679822335).testBit r.val = true := by decide

theorem even22_b29_s4_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (64000000 + (i : ZMod 347)) + 29))) = true) :
    (286682952495198494365944553418505745694082810092385814371202795628500262179846284476763693705478679822335).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_347_fin r
  change even22A347
    (-(33 * (46 * (64000000 + ((i % 347 : ℕ) : ZMod 347)) + 29))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (64000000 + (r.val : ZMod 349)) + 29))) = true →
      (1146749301848858213443599004177955455448750777150296330544177291351296520590865445022360018310471880802165).testBit r.val = true := by decide

theorem even22_b29_s4_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (64000000 + (i : ZMod 349)) + 29))) = true) :
    (1146749301848858213443599004177955455448750777150296330544177291351296520590865445022360018310471880802165).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_349_fin r
  change even22A349
    (-(33 * (46 * (64000000 + ((i % 349 : ℕ) : ZMod 349)) + 29))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB29S4Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 259339513300950594156898142077763700929808089044241450901823441437208126288396029824818147263) (.leaf 311 4171722364116706727952836270323938925372819093837903898693964234263290500302198295515419377661)) (.node (.leaf 313 8343572044316822385636437787307669781647781816606431441549844435574131614708149008653841592319) (.leaf 317 266672453714469074765305771847618997201344065029640557894301630426346340648678649545501798557462))) (.node (.node (.leaf 331 3279541095277067317754940150502837250164891098426446084345439514934247151909701251946581837075971823) (.leaf 337 271182777570219198955398471655865688270507190640582423290513311777229159198827707850578796405160116199)) (.node (.leaf 347 286682952495198494365944553418505745694082810092385814371202795628500262179846284476763693705478679822335) (.leaf 349 1146749301848858213443599004177955455448750777150296330544177291351296520590865445022360018310471880802165))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S4Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S4Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
