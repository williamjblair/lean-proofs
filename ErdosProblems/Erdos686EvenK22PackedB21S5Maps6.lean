import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s5_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (80000000 + (r.val : ZMod 401)) + 21))) = true →
      (4998065680760215231667865100265536933531114973831860204120222338292765920937780564236426476317987427821557441673472998399).testBit r.val = true := by decide

theorem even22_b21_s5_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (80000000 + (i : ZMod 401)) + 21))) = true) :
    (4998065680760215231667865100265536933531114973831860204120222338292765920937780564236426476317987427821557441673472998399).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_401_fin r
  change even22A401
    (-(33 * (46 * (80000000 + ((i % 401 : ℕ) : ZMod 401)) + 21))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (80000000 + (r.val : ZMod 409)) + 21))) = true →
      (658473718758247603585886489973277206440857193520261705274192694221889435115495495404506677387414441654917935755796301216763).testBit r.val = true := by decide

theorem even22_b21_s5_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (80000000 + (i : ZMod 409)) + 21))) = true) :
    (658473718758247603585886489973277206440857193520261705274192694221889435115495495404506677387414441654917935755796301216763).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_409_fin r
  change even22A409
    (-(33 * (46 * (80000000 + ((i % 409 : ℕ) : ZMod 409)) + 21))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (80000000 + (r.val : ZMod 419)) + 21))) = true →
      (1353593164455058467477078052158268789307856976976535785838266895961585949338490790011235485657033352552138176965994651623749535).testBit r.val = true := by decide

theorem even22_b21_s5_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (80000000 + (i : ZMod 419)) + 21))) = true) :
    (1353593164455058467477078052158268789307856976976535785838266895961585949338490790011235485657033352552138176965994651623749535).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_419_fin r
  change even22A419
    (-(33 * (46 * (80000000 + ((i % 419 : ℕ) : ZMod 419)) + 21))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (80000000 + (r.val : ZMod 421)) + 21))) = true →
      (5351907708636219003892202079749292103868574699691754328571120981807438531377093246528157158325395756906180014567160699186806523).testBit r.val = true := by decide

theorem even22_b21_s5_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (80000000 + (i : ZMod 421)) + 21))) = true) :
    (5351907708636219003892202079749292103868574699691754328571120981807438531377093246528157158325395756906180014567160699186806523).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_421_fin r
  change even22A421
    (-(33 * (46 * (80000000 + ((i % 421 : ℕ) : ZMod 421)) + 21))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (80000000 + (r.val : ZMod 431)) + 21))) = true →
      (5523677832662031719545719517123172996013537551174450920737586311892526641988565206196367948997032510784897092678730175445320441847).testBit r.val = true := by decide

theorem even22_b21_s5_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (80000000 + (i : ZMod 431)) + 21))) = true) :
    (5523677832662031719545719517123172996013537551174450920737586311892526641988565206196367948997032510784897092678730175445320441847).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_431_fin r
  change even22A431
    (-(33 * (46 * (80000000 + ((i % 431 : ℕ) : ZMod 431)) + 21))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (80000000 + (r.val : ZMod 433)) + 21))) = true →
      (22181354908742643635669588373359725474771366424740683131217176864001002742868586338204678546811939910634097782996994077413940919291).testBit r.val = true := by decide

theorem even22_b21_s5_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (80000000 + (i : ZMod 433)) + 21))) = true) :
    (22181354908742643635669588373359725474771366424740683131217176864001002742868586338204678546811939910634097782996994077413940919291).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_433_fin r
  change even22A433
    (-(33 * (46 * (80000000 + ((i % 433 : ℕ) : ZMod 433)) + 21))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (80000000 + (r.val : ZMod 439)) + 21))) = true →
      (1419519687344561341130781397752925472341539522408926058505593782063654073616344909802472983649441921089192302019933417504438361255927).testBit r.val = true := by decide

theorem even22_b21_s5_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (80000000 + (i : ZMod 439)) + 21))) = true) :
    (1419519687344561341130781397752925472341539522408926058505593782063654073616344909802472983649441921089192302019933417504438361255927).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_439_fin r
  change even22A439
    (-(33 * (46 * (80000000 + ((i % 439 : ℕ) : ZMod 439)) + 21))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (80000000 + (r.val : ZMod 443)) + 21))) = true →
      (17017780102077775193474788153393063396781469174923503872952738540086190216413783135910086918603184454377333333652581053102329742344062).testBit r.val = true := by decide

theorem even22_b21_s5_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (80000000 + (i : ZMod 443)) + 21))) = true) :
    (17017780102077775193474788153393063396781469174923503872952738540086190216413783135910086918603184454377333333652581053102329742344062).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_443_fin r
  change even22A443
    (-(33 * (46 * (80000000 + ((i % 443 : ℕ) : ZMod 443)) + 21))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB21S5Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 4998065680760215231667865100265536933531114973831860204120222338292765920937780564236426476317987427821557441673472998399) (.leaf 409 658473718758247603585886489973277206440857193520261705274192694221889435115495495404506677387414441654917935755796301216763)) (.node (.leaf 419 1353593164455058467477078052158268789307856976976535785838266895961585949338490790011235485657033352552138176965994651623749535) (.leaf 421 5351907708636219003892202079749292103868574699691754328571120981807438531377093246528157158325395756906180014567160699186806523))) (.node (.node (.leaf 431 5523677832662031719545719517123172996013537551174450920737586311892526641988565206196367948997032510784897092678730175445320441847) (.leaf 433 22181354908742643635669588373359725474771366424740683131217176864001002742868586338204678546811939910634097782996994077413940919291)) (.node (.leaf 439 1419519687344561341130781397752925472341539522408926058505593782063654073616344909802472983649441921089192302019933417504438361255927) (.leaf 443 17017780102077775193474788153393063396781469174923503872952738540086190216413783135910086918603184454377333333652581053102329742344062))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S5Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S5Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
