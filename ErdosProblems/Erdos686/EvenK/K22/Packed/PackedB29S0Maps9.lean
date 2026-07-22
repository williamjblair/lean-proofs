import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s0_map_563_fin : ∀ r : Fin 563,
    even22A563 (-(33 * (46 * (0 + (r.val : ZMod 563)) + 29))) = true →
      (20167107658599609379266320405377878004497452307033640707033679185580434049183473629481255927372902433611792039209032021145523860906846984916070520202088492278057621487613).testBit r.val = true := by decide

theorem even22_b29_s0_map_563 (i : ℕ)
    (h : even22A563 (-(33 * (46 * (0 + (i : ZMod 563)) + 29))) = true) :
    (20167107658599609379266320405377878004497452307033640707033679185580434049183473629481255927372902433611792039209032021145523860906846984916070520202088492278057621487613).testBit (i % 563) = true := by
  let r : Fin 563 := ⟨i % 563, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_563_fin r
  change even22A563
    (-(33 * (46 * (0 + ((i % 563 : ℕ) : ZMod 563)) + 29))) = true
  have hcast : (i : ZMod 563) = ((i % 563 : ℕ) : ZMod 563) :=
    (ZMod.natCast_mod i 563).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_569_fin : ∀ r : Fin 569,
    even22A569 (-(33 * (46 * (0 + (r.val : ZMod 569)) + 29))) = true →
      (1917169224499376896131478648309788316698388490089141294364718771576806038712865602804651270420292269715463166805134517149695261140961273412657619754045611604183013520179183).testBit r.val = true := by decide

theorem even22_b29_s0_map_569 (i : ℕ)
    (h : even22A569 (-(33 * (46 * (0 + (i : ZMod 569)) + 29))) = true) :
    (1917169224499376896131478648309788316698388490089141294364718771576806038712865602804651270420292269715463166805134517149695261140961273412657619754045611604183013520179183).testBit (i % 569) = true := by
  let r : Fin 569 := ⟨i % 569, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_569_fin r
  change even22A569
    (-(33 * (46 * (0 + ((i % 569 : ℕ) : ZMod 569)) + 29))) = true
  have hcast : (i : ZMod 569) = ((i % 569 : ℕ) : ZMod 569) :=
    (ZMod.natCast_mod i 569).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_571_fin : ∀ r : Fin 571,
    even22A571 (-(33 * (46 * (0 + (r.val : ZMod 571)) + 29))) = true →
      (3803667636842623788651838224092891897330726752098510128288284921595122657637939989786219227197259061345364019439774374613101987673381315744645470139318865828878767736421055).testBit r.val = true := by decide

theorem even22_b29_s0_map_571 (i : ℕ)
    (h : even22A571 (-(33 * (46 * (0 + (i : ZMod 571)) + 29))) = true) :
    (3803667636842623788651838224092891897330726752098510128288284921595122657637939989786219227197259061345364019439774374613101987673381315744645470139318865828878767736421055).testBit (i % 571) = true := by
  let r : Fin 571 := ⟨i % 571, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_571_fin r
  change even22A571
    (-(33 * (46 * (0 + ((i % 571 : ℕ) : ZMod 571)) + 29))) = true
  have hcast : (i : ZMod 571) = ((i % 571 : ℕ) : ZMod 571) :=
    (ZMod.natCast_mod i 571).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_577_fin : ∀ r : Fin 577,
    even22A577 (-(33 * (46 * (0 + (r.val : ZMod 577)) + 29))) = true →
      (492245229271661908140653271561524348244791698480257635527574911454001975559287956501506527143653354647346507794061743940504555183050934637611883863573524750246811406794881759).testBit r.val = true := by decide

theorem even22_b29_s0_map_577 (i : ℕ)
    (h : even22A577 (-(33 * (46 * (0 + (i : ZMod 577)) + 29))) = true) :
    (492245229271661908140653271561524348244791698480257635527574911454001975559287956501506527143653354647346507794061743940504555183050934637611883863573524750246811406794881759).testBit (i % 577) = true := by
  let r : Fin 577 := ⟨i % 577, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_577_fin r
  change even22A577
    (-(33 * (46 * (0 + ((i % 577 : ℕ) : ZMod 577)) + 29))) = true
  have hcast : (i : ZMod 577) = ((i % 577 : ℕ) : ZMod 577) :=
    (ZMod.natCast_mod i 577).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_587_fin : ∀ r : Fin 587,
    even22A587 (-(33 * (46 * (0 + (r.val : ZMod 587)) + 29))) = true →
      (441237413487844234238132409002871587816517218672511088663147187370182842991356233637709396611424130960793225621845202788323298438008377505994203442950547204096984871242788700143).testBit r.val = true := by decide

theorem even22_b29_s0_map_587 (i : ℕ)
    (h : even22A587 (-(33 * (46 * (0 + (i : ZMod 587)) + 29))) = true) :
    (441237413487844234238132409002871587816517218672511088663147187370182842991356233637709396611424130960793225621845202788323298438008377505994203442950547204096984871242788700143).testBit (i % 587) = true := by
  let r : Fin 587 := ⟨i % 587, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_587_fin r
  change even22A587
    (-(33 * (46 * (0 + ((i % 587 : ℕ) : ZMod 587)) + 29))) = true
  have hcast : (i : ZMod 587) = ((i % 587 : ℕ) : ZMod 587) :=
    (ZMod.natCast_mod i 587).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_593_fin : ∀ r : Fin 593,
    even22A593 (-(33 * (46 * (0 + (r.val : ZMod 593)) + 29))) = true →
      (31206600378240043683978621947978700748425315682217176758801931353693990508819243724278808102274920794222161213694632435654217377641202522747542729848354361844483696166861091897301).testBit r.val = true := by decide

theorem even22_b29_s0_map_593 (i : ℕ)
    (h : even22A593 (-(33 * (46 * (0 + (i : ZMod 593)) + 29))) = true) :
    (31206600378240043683978621947978700748425315682217176758801931353693990508819243724278808102274920794222161213694632435654217377641202522747542729848354361844483696166861091897301).testBit (i % 593) = true := by
  let r : Fin 593 := ⟨i % 593, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_593_fin r
  change even22A593
    (-(33 * (46 * (0 + ((i % 593 : ℕ) : ZMod 593)) + 29))) = true
  have hcast : (i : ZMod 593) = ((i % 593 : ℕ) : ZMod 593) :=
    (ZMod.natCast_mod i 593).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_599_fin : ∀ r : Fin 599,
    even22A599 (-(33 * (46 * (0 + (r.val : ZMod 599)) + 29))) = true →
      (2074753819121989870369964713736553550632969869778827358846713106050989537066164168181045180610876346278610271152808201005363389919700996012710560047052648240184191811205200158388191).testBit r.val = true := by decide

theorem even22_b29_s0_map_599 (i : ℕ)
    (h : even22A599 (-(33 * (46 * (0 + (i : ZMod 599)) + 29))) = true) :
    (2074753819121989870369964713736553550632969869778827358846713106050989537066164168181045180610876346278610271152808201005363389919700996012710560047052648240184191811205200158388191).testBit (i % 599) = true := by
  let r : Fin 599 := ⟨i % 599, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_599_fin r
  change even22A599
    (-(33 * (46 * (0 + ((i % 599 : ℕ) : ZMod 599)) + 29))) = true
  have hcast : (i : ZMod 599) = ((i % 599 : ℕ) : ZMod 599) :=
    (ZMod.natCast_mod i 599).symm
  rw [← hcast]
  exact h


theorem even22_b29_s0_map_601_fin : ∀ r : Fin 601,
    even22A601 (-(33 * (46 * (0 + (r.val : ZMod 601)) + 29))) = true →
      (8233656766041666518380985885337139748554576114939667911859679500402040345262606443099103868273666519688177774817937693525861169677232508635681940266753238253959545570745630519130623).testBit r.val = true := by decide

theorem even22_b29_s0_map_601 (i : ℕ)
    (h : even22A601 (-(33 * (46 * (0 + (i : ZMod 601)) + 29))) = true) :
    (8233656766041666518380985885337139748554576114939667911859679500402040345262606443099103868273666519688177774817937693525861169677232508635681940266753238253959545570745630519130623).testBit (i % 601) = true := by
  let r : Fin 601 := ⟨i % 601, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s0_map_601_fin r
  change even22A601
    (-(33 * (46 * (0 + ((i % 601 : ℕ) : ZMod 601)) + 29))) = true
  have hcast : (i : ZMod 601) = ((i % 601 : ℕ) : ZMod 601) :=
    (ZMod.natCast_mod i 601).symm
  rw [← hcast]
  exact h

def even22PackedB29S0Group9Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 563 20167107658599609379266320405377878004497452307033640707033679185580434049183473629481255927372902433611792039209032021145523860906846984916070520202088492278057621487613) (.leaf 569 1917169224499376896131478648309788316698388490089141294364718771576806038712865602804651270420292269715463166805134517149695261140961273412657619754045611604183013520179183)) (.node (.leaf 571 3803667636842623788651838224092891897330726752098510128288284921595122657637939989786219227197259061345364019439774374613101987673381315744645470139318865828878767736421055) (.leaf 577 492245229271661908140653271561524348244791698480257635527574911454001975559287956501506527143653354647346507794061743940504555183050934637611883863573524750246811406794881759))) (.node (.node (.leaf 587 441237413487844234238132409002871587816517218672511088663147187370182842991356233637709396611424130960793225621845202788323298438008377505994203442950547204096984871242788700143) (.leaf 593 31206600378240043683978621947978700748425315682217176758801931353693990508819243724278808102274920794222161213694632435654217377641202522747542729848354361844483696166861091897301)) (.node (.leaf 599 2074753819121989870369964713736553550632969869778827358846713106050989537066164168181045180610876346278610271152808201005363389919700996012710560047052648240184191811205200158388191) (.leaf 601 8233656766041666518380985885337139748554576114939667911859679500402040345262606443099103868273666519688177774817937693525861169677232508635681940266753238253959545570745630519130623))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S0Group9TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S0Group9Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_563 i
          have hA := even22_allowed_int even22A563 even22_allowed_563 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_569 i
          have hA := even22_allowed_int even22A569 even22_allowed_569 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_571 i
          have hA := even22_allowed_int even22A571 even22_allowed_571 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_577 i
          have hA := even22_allowed_int even22A577 even22_allowed_577 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_587 i
          have hA := even22_allowed_int even22A587 even22_allowed_587 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_593 i
          have hA := even22_allowed_int even22A593 even22_allowed_593 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_599 i
          have hA := even22_allowed_int even22A599 even22_allowed_599 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s0_map_601 i
          have hA := even22_allowed_int even22A601 even22_allowed_601 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
