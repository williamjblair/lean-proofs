import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s1_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (16000000 + (r.val : ZMod 401)) + 17))) = true →
      (5154372824924923569616328372949078382424861437258283485980533044037297015091522357476562368840672559193835707923760676863).testBit r.val = true := by decide

theorem even22_b17_s1_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (16000000 + (i : ZMod 401)) + 17))) = true) :
    (5154372824924923569616328372949078382424861437258283485980533044037297015091522357476562368840672559193835707923760676863).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_401_fin r
  change even22A401
    (-(33 * (46 * (16000000 + ((i % 401 : ℕ) : ZMod 401)) + 17))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (16000000 + (r.val : ZMod 409)) + 17))) = true →
      (1322101822327479550462626818080293403574652916453035812764192290067767420911388409366833134620385285815151349378961020813311).testBit r.val = true := by decide

theorem even22_b17_s1_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (16000000 + (i : ZMod 409)) + 17))) = true) :
    (1322101822327479550462626818080293403574652916453035812764192290067767420911388409366833134620385285815151349378961020813311).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_409_fin r
  change even22A409
    (-(33 * (46 * (16000000 + ((i % 409 : ℕ) : ZMod 409)) + 17))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (16000000 + (r.val : ZMod 419)) + 17))) = true →
      (1353756118708587649105403770157330691406324850754693209624534565065354139257720066306198660509806857536774111107294480891371518).testBit r.val = true := by decide

theorem even22_b17_s1_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (16000000 + (i : ZMod 419)) + 17))) = true) :
    (1353756118708587649105403770157330691406324850754693209624534565065354139257720066306198660509806857536774111107294480891371518).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_419_fin r
  change even22A419
    (-(33 * (46 * (16000000 + ((i % 419 : ℕ) : ZMod 419)) + 17))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (16000000 + (r.val : ZMod 421)) + 17))) = true →
      (3870895853453545877523391976747312251844798193727980616118648788615677228599764467514716561913453784664488818538140165155586005).testBit r.val = true := by decide

theorem even22_b17_s1_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (16000000 + (i : ZMod 421)) + 17))) = true) :
    (3870895853453545877523391976747312251844798193727980616118648788615677228599764467514716561913453784664488818538140165155586005).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_421_fin r
  change even22A421
    (-(33 * (46 * (16000000 + ((i % 421 : ℕ) : ZMod 421)) + 17))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (16000000 + (r.val : ZMod 431)) + 17))) = true →
      (5534507035924967517328919825256086093069122757306177286618037887388239249635217643831090554523311903752645423936483110509908836351).testBit r.val = true := by decide

theorem even22_b17_s1_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (16000000 + (i : ZMod 431)) + 17))) = true) :
    (5534507035924967517328919825256086093069122757306177286618037887388239249635217643831090554523311903752645423936483110509908836351).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_431_fin r
  change even22A431
    (-(33 * (46 * (16000000 + ((i % 431 : ℕ) : ZMod 431)) + 17))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (16000000 + (r.val : ZMod 433)) + 17))) = true →
      (22180996573149633473705190218236128891821869218320234046791340571726657177583304317653114614755326802589629715496561712178346844127).testBit r.val = true := by decide

theorem even22_b17_s1_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (16000000 + (i : ZMod 433)) + 17))) = true) :
    (22180996573149633473705190218236128891821869218320234046791340571726657177583304317653114614755326802589629715496561712178346844127).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_433_fin r
  change even22A433
    (-(33 * (46 * (16000000 + ((i % 433 : ℕ) : ZMod 433)) + 17))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (16000000 + (r.val : ZMod 439)) + 17))) = true →
      (1388928259033710657998469438324788731676374839438019438580763034225975301634506279457212652899545274191542226774981798415913917079545).testBit r.val = true := by decide

theorem even22_b17_s1_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (16000000 + (i : ZMod 439)) + 17))) = true) :
    (1388928259033710657998469438324788731676374839438019438580763034225975301634506279457212652899545274191542226774981798415913917079545).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_439_fin r
  change even22A439
    (-(33 * (46 * (16000000 + ((i % 439 : ℕ) : ZMod 439)) + 17))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b17_s1_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (16000000 + (r.val : ZMod 443)) + 17))) = true →
      (11256854834201019443952004777331726103634741491760951306938293661605833255802921400976674879441523773640565314397380846725674433117887).testBit r.val = true := by decide

theorem even22_b17_s1_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (16000000 + (i : ZMod 443)) + 17))) = true) :
    (11256854834201019443952004777331726103634741491760951306938293661605833255802921400976674879441523773640565314397380846725674433117887).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s1_map_443_fin r
  change even22A443
    (-(33 * (46 * (16000000 + ((i % 443 : ℕ) : ZMod 443)) + 17))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB17S1Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5154372824924923569616328372949078382424861437258283485980533044037297015091522357476562368840672559193835707923760676863) (.leaf 409 1322101822327479550462626818080293403574652916453035812764192290067767420911388409366833134620385285815151349378961020813311)) (.node (.leaf 419 1353756118708587649105403770157330691406324850754693209624534565065354139257720066306198660509806857536774111107294480891371518) (.leaf 421 3870895853453545877523391976747312251844798193727980616118648788615677228599764467514716561913453784664488818538140165155586005))) (.node (.node (.leaf 431 5534507035924967517328919825256086093069122757306177286618037887388239249635217643831090554523311903752645423936483110509908836351) (.leaf 433 22180996573149633473705190218236128891821869218320234046791340571726657177583304317653114614755326802589629715496561712178346844127)) (.node (.leaf 439 1388928259033710657998469438324788731676374839438019438580763034225975301634506279457212652899545274191542226774981798415913917079545) (.leaf 443 11256854834201019443952004777331726103634741491760951306938293661605833255802921400976674879441523773640565314397380846725674433117887))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S1Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S1Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s1_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
