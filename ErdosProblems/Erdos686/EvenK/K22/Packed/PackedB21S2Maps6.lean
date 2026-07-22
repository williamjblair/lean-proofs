import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s2_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (32000000 + (r.val : ZMod 401)) + 21))) = true →
      (5158195391760032849394262853724806682870229826943639485199434226223802746379253657812294027686590544276139458166679142399).testBit r.val = true := by decide

theorem even22_b21_s2_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (32000000 + (i : ZMod 401)) + 21))) = true) :
    (5158195391760032849394262853724806682870229826943639485199434226223802746379253657812294027686590544276139458166679142399).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_401_fin r
  change even22A401
    (-(33 * (46 * (32000000 + ((i % 401 : ℕ) : ZMod 401)) + 21))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (32000000 + (r.val : ZMod 409)) + 21))) = true →
      (1322111917824143647811172014897602140836336404113180550628271994258809543094573405942793371492205871875104238357329752358911).testBit r.val = true := by decide

theorem even22_b21_s2_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (32000000 + (i : ZMod 409)) + 21))) = true) :
    (1322111917824143647811172014897602140836336404113180550628271994258809543094573405942793371492205871875104238357329752358911).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_409_fin r
  change even22A409
    (-(33 * (46 * (32000000 + ((i % 409 : ℕ) : ZMod 409)) + 21))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (32000000 + (r.val : ZMod 419)) + 21))) = true →
      (1353744458239099645451159074231071051120237197984440121837116734168218997698309649686151069938461440884409298688811008683669407).testBit r.val = true := by decide

theorem even22_b21_s2_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (32000000 + (i : ZMod 419)) + 21))) = true) :
    (1353744458239099645451159074231071051120237197984440121837116734168218997698309649686151069938461440884409298688811008683669407).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_419_fin r
  change even22A419
    (-(33 * (46 * (32000000 + ((i % 419 : ℕ) : ZMod 419)) + 21))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (32000000 + (r.val : ZMod 421)) + 21))) = true →
      (4061526457557425892808509653485144351075792827904843345332819477508836788605772071353985912544292987366357418484905714319095514).testBit r.val = true := by decide

theorem even22_b21_s2_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (32000000 + (i : ZMod 421)) + 21))) = true) :
    (4061526457557425892808509653485144351075792827904843345332819477508836788605772071353985912544292987366357418484905714319095514).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_421_fin r
  change even22A421
    (-(33 * (46 * (32000000 + ((i % 421 : ℕ) : ZMod 421)) + 21))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (32000000 + (r.val : ZMod 431)) + 21))) = true →
      (5518157840940189270091619405870805658992205891969738984392900895122609532441523401453105083950453140914503361643445683402506764139).testBit r.val = true := by decide

theorem even22_b21_s2_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (32000000 + (i : ZMod 431)) + 21))) = true) :
    (5518157840940189270091619405870805658992205891969738984392900895122609532441523401453105083950453140914503361643445683402506764139).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_431_fin r
  change even22A431
    (-(33 * (46 * (32000000 + ((i % 431 : ℕ) : ZMod 431)) + 21))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (32000000 + (r.val : ZMod 433)) + 21))) = true →
      (21488189776916962734581418791117777079820209963669720744139017046566840220176350824002509967000365138631549951384281327316685029367).testBit r.val = true := by decide

theorem even22_b21_s2_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (32000000 + (i : ZMod 433)) + 21))) = true) :
    (21488189776916962734581418791117777079820209963669720744139017046566840220176350824002509967000365138631549951384281327316685029367).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_433_fin r
  change even22A433
    (-(33 * (46 * (32000000 + ((i % 433 : ℕ) : ZMod 433)) + 21))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (32000000 + (r.val : ZMod 439)) + 21))) = true →
      (1419597406398527633024445110590244993729647871692180073999496517028778018688171564635238309459090564119978962962742345742570205904639).testBit r.val = true := by decide

theorem even22_b21_s2_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (32000000 + (i : ZMod 439)) + 21))) = true) :
    (1419597406398527633024445110590244993729647871692180073999496517028778018688171564635238309459090564119978962962742345742570205904639).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_439_fin r
  change even22A439
    (-(33 * (46 * (32000000 + ((i % 439 : ℕ) : ZMod 439)) + 21))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b21_s2_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (32000000 + (r.val : ZMod 443)) + 21))) = true →
      (22491546923231364450718036707587201825530927221249719097514471548282026641921623336457969928842190304289644276283816711040966454148787).testBit r.val = true := by decide

theorem even22_b21_s2_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (32000000 + (i : ZMod 443)) + 21))) = true) :
    (22491546923231364450718036707587201825530927221249719097514471548282026641921623336457969928842190304289644276283816711040966454148787).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s2_map_443_fin r
  change even22A443
    (-(33 * (46 * (32000000 + ((i % 443 : ℕ) : ZMod 443)) + 21))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB21S2Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5158195391760032849394262853724806682870229826943639485199434226223802746379253657812294027686590544276139458166679142399) (.leaf 409 1322111917824143647811172014897602140836336404113180550628271994258809543094573405942793371492205871875104238357329752358911)) (.node (.leaf 419 1353744458239099645451159074231071051120237197984440121837116734168218997698309649686151069938461440884409298688811008683669407) (.leaf 421 4061526457557425892808509653485144351075792827904843345332819477508836788605772071353985912544292987366357418484905714319095514))) (.node (.node (.leaf 431 5518157840940189270091619405870805658992205891969738984392900895122609532441523401453105083950453140914503361643445683402506764139) (.leaf 433 21488189776916962734581418791117777079820209963669720744139017046566840220176350824002509967000365138631549951384281327316685029367)) (.node (.leaf 439 1419597406398527633024445110590244993729647871692180073999496517028778018688171564635238309459090564119978962962742345742570205904639) (.leaf 443 22491546923231364450718036707587201825530927221249719097514471548282026641921623336457969928842190304289644276283816711040966454148787))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S2Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S2Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s2_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
