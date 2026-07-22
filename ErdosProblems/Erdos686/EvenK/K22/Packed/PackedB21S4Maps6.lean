import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s4_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (64000000 + (r.val : ZMod 401)) + 21))) = true →
      (3590231997596937650773395641129879672362265588655900883941084898627888479684683707642381546350070020402946495676873110971).testBit r.val = true := by decide

theorem even22_b21_s4_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (64000000 + (i : ZMod 401)) + 21))) = true) :
    (3590231997596937650773395641129879672362265588655900883941084898627888479684683707642381546350070020402946495676873110971).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_401_fin r
  change even22A401
    (-(33 * (46 * (64000000 + ((i % 401 : ℕ) : ZMod 401)) + 21))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (64000000 + (r.val : ZMod 409)) + 21))) = true →
      (658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423).testBit r.val = true := by decide

theorem even22_b21_s4_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (64000000 + (i : ZMod 409)) + 21))) = true) :
    (658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_409_fin r
  change even22A409
    (-(33 * (46 * (64000000 + ((i % 409 : ℕ) : ZMod 409)) + 21))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (64000000 + (r.val : ZMod 419)) + 21))) = true →
      (1353512086011042523616565844664806247233288393434661790656546797575053624612316397169927007136977389073811540843846736587243495).testBit r.val = true := by decide

theorem even22_b21_s4_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (64000000 + (i : ZMod 419)) + 21))) = true) :
    (1353512086011042523616565844664806247233288393434661790656546797575053624612316397169927007136977389073811540843846736587243495).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_419_fin r
  change even22A419
    (-(33 * (46 * (64000000 + ((i % 419 : ℕ) : ZMod 419)) + 21))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (64000000 + (r.val : ZMod 421)) + 21))) = true →
      (5415360167330050034840068590974388511917282791435037718205946320552213745044421266874109689927292471403476303198013628612607997).testBit r.val = true := by decide

theorem even22_b21_s4_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (64000000 + (i : ZMod 421)) + 21))) = true) :
    (5415360167330050034840068590974388511917282791435037718205946320552213745044421266874109689927292471403476303198013628612607997).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_421_fin r
  change even22A421
    (-(33 * (46 * (64000000 + ((i % 421 : ℕ) : ZMod 421)) + 21))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (64000000 + (r.val : ZMod 431)) + 21))) = true →
      (5539921373512441164987777375146829963798430506976536684589942187823582135032819520492970886016765791949791193321168162442436082444).testBit r.val = true := by decide

theorem even22_b21_s4_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (64000000 + (i : ZMod 431)) + 21))) = true) :
    (5539921373512441164987777375146829963798430506976536684589942187823582135032819520492970886016765791949791193321168162442436082444).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_431_fin r
  change even22A431
    (-(33 * (46 * (64000000 + ((i % 431 : ℕ) : ZMod 431)) + 21))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (64000000 + (r.val : ZMod 433)) + 21))) = true →
      (21834773664941740805604366132131223353655853283338126672751426845741905341310677904161152607916740881705339819537754950974239145979).testBit r.val = true := by decide

theorem even22_b21_s4_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (64000000 + (i : ZMod 433)) + 21))) = true) :
    (21834773664941740805604366132131223353655853283338126672751426845741905341310677904161152607916740881705339819537754950974239145979).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_433_fin r
  change even22A433
    (-(33 * (46 * (64000000 + ((i % 433 : ℕ) : ZMod 433)) + 21))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (64000000 + (r.val : ZMod 439)) + 21))) = true →
      (1407129869435512520329950227657360597754380604703676907980640502134909650709971947666656853343620560672979496324799763769669023956095).testBit r.val = true := by decide

theorem even22_b21_s4_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (64000000 + (i : ZMod 439)) + 21))) = true) :
    (1407129869435512520329950227657360597754380604703676907980640502134909650709971947666656853343620560672979496324799763769669023956095).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_439_fin r
  change even22A439
    (-(33 * (46 * (64000000 + ((i % 439 : ℕ) : ZMod 439)) + 21))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (64000000 + (r.val : ZMod 443)) + 21))) = true →
      (21910972755264243539252121655669497647267561726521405536391584084512776670666742510278779669876252352265735130422890541096236272320433).testBit r.val = true := by decide

theorem even22_b21_s4_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (64000000 + (i : ZMod 443)) + 21))) = true) :
    (21910972755264243539252121655669497647267561726521405536391584084512776670666742510278779669876252352265735130422890541096236272320433).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_443_fin r
  change even22A443
    (-(33 * (46 * (64000000 + ((i % 443 : ℕ) : ZMod 443)) + 21))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB21S4Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 3590231997596937650773395641129879672362265588655900883941084898627888479684683707642381546350070020402946495676873110971) (.leaf 409 658149676755484649561909517281733187290277058225425630562133236936008821298843687970441939605808819015780528075335924711423)) (.node (.leaf 419 1353512086011042523616565844664806247233288393434661790656546797575053624612316397169927007136977389073811540843846736587243495) (.leaf 421 5415360167330050034840068590974388511917282791435037718205946320552213745044421266874109689927292471403476303198013628612607997))) (.node (.node (.leaf 431 5539921373512441164987777375146829963798430506976536684589942187823582135032819520492970886016765791949791193321168162442436082444) (.leaf 433 21834773664941740805604366132131223353655853283338126672751426845741905341310677904161152607916740881705339819537754950974239145979)) (.node (.leaf 439 1407129869435512520329950227657360597754380604703676907980640502134909650709971947666656853343620560672979496324799763769669023956095) (.leaf 443 21910972755264243539252121655669497647267561726521405536391584084512776670666742510278779669876252352265735130422890541096236272320433))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S4Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S4Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
