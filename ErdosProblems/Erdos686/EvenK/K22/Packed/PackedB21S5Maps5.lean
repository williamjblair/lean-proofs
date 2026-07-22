import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s5_map_353_fin : ∀ r : Fin 353,
    even22A353 (-(33 * (46 * (80000000 + (r.val : ZMod 353)) + 21))) = true →
      (18347967055404456996407906611157791061807555947933407237079919954016403182045253725225591248505778636586997).testBit r.val = true := by decide

theorem even22_b21_s5_map_353 (i : ℕ)
    (h : even22A353 (-(33 * (46 * (80000000 + (i : ZMod 353)) + 21))) = true) :
    (18347967055404456996407906611157791061807555947933407237079919954016403182045253725225591248505778636586997).testBit (i % 353) = true := by
  let r : Fin 353 := ⟨i % 353, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_353_fin r
  change even22A353
    (-(33 * (46 * (80000000 + ((i % 353 : ℕ) : ZMod 353)) + 21))) = true
  have hcast : (i : ZMod 353) = ((i % 353 : ℕ) : ZMod 353) :=
    (ZMod.natCast_mod i 353).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_359_fin : ∀ r : Fin 359,
    even22A359 (-(33 * (46 * (80000000 + (r.val : ZMod 359)) + 21))) = true →
      (1173405559947243791630170259009488131549240653044416508017348051800445597955135734001154737935971953423416126).testBit r.val = true := by decide

theorem even22_b21_s5_map_359 (i : ℕ)
    (h : even22A359 (-(33 * (46 * (80000000 + (i : ZMod 359)) + 21))) = true) :
    (1173405559947243791630170259009488131549240653044416508017348051800445597955135734001154737935971953423416126).testBit (i % 359) = true := by
  let r : Fin 359 := ⟨i % 359, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_359_fin r
  change even22A359
    (-(33 * (46 * (80000000 + ((i % 359 : ℕ) : ZMod 359)) + 21))) = true
  have hcast : (i : ZMod 359) = ((i % 359 : ℕ) : ZMod 359) :=
    (ZMod.natCast_mod i 359).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_367_fin : ∀ r : Fin 367,
    even22A367 (-(33 * (46 * (80000000 + (r.val : ZMod 367)) + 21))) = true →
      (298224771784275567073306384052203842991369112488257247399717023838852375486928016598507807642338714373651947517).testBit r.val = true := by decide

theorem even22_b21_s5_map_367 (i : ℕ)
    (h : even22A367 (-(33 * (46 * (80000000 + (i : ZMod 367)) + 21))) = true) :
    (298224771784275567073306384052203842991369112488257247399717023838852375486928016598507807642338714373651947517).testBit (i % 367) = true := by
  let r : Fin 367 := ⟨i % 367, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_367_fin r
  change even22A367
    (-(33 * (46 * (80000000 + ((i % 367 : ℕ) : ZMod 367)) + 21))) = true
  have hcast : (i : ZMod 367) = ((i % 367 : ℕ) : ZMod 367) :=
    (ZMod.natCast_mod i 367).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_373_fin : ∀ r : Fin 373,
    even22A373 (-(33 * (46 * (80000000 + (r.val : ZMod 373)) + 21))) = true →
      (9582053164305126634121794044891747676784856398516662310379558361525446527501674887749753358306107214046652922855).testBit r.val = true := by decide

theorem even22_b21_s5_map_373 (i : ℕ)
    (h : even22A373 (-(33 * (46 * (80000000 + (i : ZMod 373)) + 21))) = true) :
    (9582053164305126634121794044891747676784856398516662310379558361525446527501674887749753358306107214046652922855).testBit (i % 373) = true := by
  let r : Fin 373 := ⟨i % 373, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_373_fin r
  change even22A373
    (-(33 * (46 * (80000000 + ((i % 373 : ℕ) : ZMod 373)) + 21))) = true
  have hcast : (i : ZMod 373) = ((i % 373 : ℕ) : ZMod 373) :=
    (ZMod.natCast_mod i 373).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_379_fin : ∀ r : Fin 379,
    even22A379 (-(33 * (46 * (80000000 + (r.val : ZMod 379)) + 21))) = true →
      (1211472203604345471861187913994008063320385952344827036809061156112572905944541568723719246695889530035983779626991).testBit r.val = true := by decide

theorem even22_b21_s5_map_379 (i : ℕ)
    (h : even22A379 (-(33 * (46 * (80000000 + (i : ZMod 379)) + 21))) = true) :
    (1211472203604345471861187913994008063320385952344827036809061156112572905944541568723719246695889530035983779626991).testBit (i % 379) = true := by
  let r : Fin 379 := ⟨i % 379, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_379_fin r
  change even22A379
    (-(33 * (46 * (80000000 + ((i % 379 : ℕ) : ZMod 379)) + 21))) = true
  have hcast : (i : ZMod 379) = ((i % 379 : ℕ) : ZMod 379) :=
    (ZMod.natCast_mod i 379).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_383_fin : ∀ r : Fin 383,
    even22A383 (-(33 * (46 * (80000000 + (r.val : ZMod 383)) + 21))) = true →
      (18468487290229300046903726397081435829732060957074089308522570618270346732675073353438434596328164975476974689386430).testBit r.val = true := by decide

theorem even22_b21_s5_map_383 (i : ℕ)
    (h : even22A383 (-(33 * (46 * (80000000 + (i : ZMod 383)) + 21))) = true) :
    (18468487290229300046903726397081435829732060957074089308522570618270346732675073353438434596328164975476974689386430).testBit (i % 383) = true := by
  let r : Fin 383 := ⟨i % 383, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_383_fin r
  change even22A383
    (-(33 * (46 * (80000000 + ((i % 383 : ℕ) : ZMod 383)) + 21))) = true
  have hcast : (i : ZMod 383) = ((i % 383 : ℕ) : ZMod 383) :=
    (ZMod.natCast_mod i 383).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_389_fin : ∀ r : Fin 389,
    even22A389 (-(33 * (46 * (80000000 + (r.val : ZMod 389)) + 21))) = true →
      (1260864197697487689031118347093861326721894573966693277660295841291322797751562583629905163739178359580646170964262911).testBit r.val = true := by decide

theorem even22_b21_s5_map_389 (i : ℕ)
    (h : even22A389 (-(33 * (46 * (80000000 + (i : ZMod 389)) + 21))) = true) :
    (1260864197697487689031118347093861326721894573966693277660295841291322797751562583629905163739178359580646170964262911).testBit (i % 389) = true := by
  let r : Fin 389 := ⟨i % 389, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_389_fin r
  change even22A389
    (-(33 * (46 * (80000000 + ((i % 389 : ℕ) : ZMod 389)) + 21))) = true
  have hcast : (i : ZMod 389) = ((i % 389 : ℕ) : ZMod 389) :=
    (ZMod.natCast_mod i 389).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_397_fin : ∀ r : Fin 397,
    even22A397 (-(33 * (46 * (80000000 + (r.val : ZMod 397)) + 21))) = true →
      (302585243957473265497415119601827677122694209090980905290131595024926289601696535392593403134153923223330652575521308095).testBit r.val = true := by decide

theorem even22_b21_s5_map_397 (i : ℕ)
    (h : even22A397 (-(33 * (46 * (80000000 + (i : ZMod 397)) + 21))) = true) :
    (302585243957473265497415119601827677122694209090980905290131595024926289601696535392593403134153923223330652575521308095).testBit (i % 397) = true := by
  let r : Fin 397 := ⟨i % 397, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_397_fin r
  change even22A397
    (-(33 * (46 * (80000000 + ((i % 397 : ℕ) : ZMod 397)) + 21))) = true
  have hcast : (i : ZMod 397) = ((i % 397 : ℕ) : ZMod 397) :=
    (ZMod.natCast_mod i 397).symm
  rw [← hcast]
  exact h

def even22PackedB21S5Group5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 353 18347967055404456996407906611157791061807555947933407237079919954016403182045253725225591248505778636586997) (.leaf 359 1173405559947243791630170259009488131549240653044416508017348051800445597955135734001154737935971953423416126)) (.node (.leaf 367 298224771784275567073306384052203842991369112488257247399717023838852375486928016598507807642338714373651947517) (.leaf 373 9582053164305126634121794044891747676784856398516662310379558361525446527501674887749753358306107214046652922855))) (.node (.node (.leaf 379 1211472203604345471861187913994008063320385952344827036809061156112572905944541568723719246695889530035983779626991) (.leaf 383 18468487290229300046903726397081435829732060957074089308522570618270346732675073353438434596328164975476974689386430)) (.node (.leaf 389 1260864197697487689031118347093861326721894573966693277660295841291322797751562583629905163739178359580646170964262911) (.leaf 397 302585243957473265497415119601827677122694209090980905290131595024926289601696535392593403134153923223330652575521308095))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S5Group5TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S5Group5Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_353 i
          have hA := even22_allowed_int even22A353 even22_allowed_353 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_359 i
          have hA := even22_allowed_int even22A359 even22_allowed_359 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_367 i
          have hA := even22_allowed_int even22A367 even22_allowed_367 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_373 i
          have hA := even22_allowed_int even22A373 even22_allowed_373 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_379 i
          have hA := even22_allowed_int even22A379 even22_allowed_379 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_383 i
          have hA := even22_allowed_int even22A383 even22_allowed_383 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_389 i
          have hA := even22_allowed_int even22A389 even22_allowed_389 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_397 i
          have hA := even22_allowed_int even22A397 even22_allowed_397 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
