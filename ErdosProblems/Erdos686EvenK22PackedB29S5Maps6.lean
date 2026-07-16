import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s5_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (80000000 + (r.val : ZMod 401)) + 29))) = true →
      (3507532028270573963154605725506181639827230092359203699296613413790267740605353981342416574968403757638703813215877134327).testBit r.val = true := by decide

theorem even22_b29_s5_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (80000000 + (i : ZMod 401)) + 29))) = true) :
    (3507532028270573963154605725506181639827230092359203699296613413790267740605353981342416574968403757638703813215877134327).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_401_fin r
  change even22A401
    (-(33 * (46 * (80000000 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (80000000 + (r.val : ZMod 409)) + 29))) = true →
      (1239479901925720686573012297182456512093143729457639167708870314644151833008078828362692790158500365172152032614675180814334).testBit r.val = true := by decide

theorem even22_b29_s5_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (80000000 + (i : ZMod 409)) + 29))) = true) :
    (1239479901925720686573012297182456512093143729457639167708870314644151833008078828362692790158500365172152032614675180814334).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_409_fin r
  change even22A409
    (-(33 * (46 * (80000000 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (80000000 + (r.val : ZMod 419)) + 29))) = true →
      (1309551872675590578016706835633503230497627533159627472236762892527975408998233825030100157966753437848408948811129096945794559).testBit r.val = true := by decide

theorem even22_b29_s5_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (80000000 + (i : ZMod 419)) + 29))) = true) :
    (1309551872675590578016706835633503230497627533159627472236762892527975408998233825030100157966753437848408948811129096945794559).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_419_fin r
  change even22A419
    (-(33 * (46 * (80000000 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (80000000 + (r.val : ZMod 421)) + 29))) = true →
      (5076909517527869662207771390303241840683491453559168700663168478634445273671013595996020626114674164439875792548711337944940543).testBit r.val = true := by decide

theorem even22_b29_s5_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (80000000 + (i : ZMod 421)) + 29))) = true) :
    (5076909517527869662207771390303241840683491453559168700663168478634445273671013595996020626114674164439875792548711337944940543).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_421_fin r
  change even22A421
    (-(33 * (46 * (80000000 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (80000000 + (r.val : ZMod 431)) + 29))) = true →
      (5544662135879284957223684216941629861809407749541247793410607896911359232568277375930595780324921543731550456765631162719011862079).testBit r.val = true := by decide

theorem even22_b29_s5_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (80000000 + (i : ZMod 431)) + 29))) = true) :
    (5544662135879284957223684216941629861809407749541247793410607896911359232568277375930595780324921543731550456765631162719011862079).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_431_fin r
  change even22A431
    (-(33 * (46 * (80000000 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (80000000 + (r.val : ZMod 433)) + 29))) = true →
      (22137865358662827384011778049912605370210738739698448148994771988219209762976176703789768117499760787783075819681944980101270532095).testBit r.val = true := by decide

theorem even22_b29_s5_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (80000000 + (i : ZMod 433)) + 29))) = true) :
    (22137865358662827384011778049912605370210738739698448148994771988219209762976176703789768117499760787783075819681944980101270532095).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_433_fin r
  change even22A433
    (-(33 * (46 * (80000000 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (80000000 + (r.val : ZMod 439)) + 29))) = true →
      (1418215003326442557777578803765237018634549750056563872889687227406773199289111469732376077254825169153804741707174940037535720431592).testBit r.val = true := by decide

theorem even22_b29_s5_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (80000000 + (i : ZMod 439)) + 29))) = true) :
    (1418215003326442557777578803765237018634549750056563872889687227406773199289111469732376077254825169153804741707174940037535720431592).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_439_fin r
  change even22A439
    (-(33 * (46 * (80000000 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (80000000 + (r.val : ZMod 443)) + 29))) = true →
      (22346135419111066841513158697972887567714515734033473996238498651436324301290265557893192769861155991400173046453165691533561935429627).testBit r.val = true := by decide

theorem even22_b29_s5_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (80000000 + (i : ZMod 443)) + 29))) = true) :
    (22346135419111066841513158697972887567714515734033473996238498651436324301290265557893192769861155991400173046453165691533561935429627).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_443_fin r
  change even22A443
    (-(33 * (46 * (80000000 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S5Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 3507532028270573963154605725506181639827230092359203699296613413790267740605353981342416574968403757638703813215877134327) (.leaf 409 1239479901925720686573012297182456512093143729457639167708870314644151833008078828362692790158500365172152032614675180814334)) (.node (.leaf 419 1309551872675590578016706835633503230497627533159627472236762892527975408998233825030100157966753437848408948811129096945794559) (.leaf 421 5076909517527869662207771390303241840683491453559168700663168478634445273671013595996020626114674164439875792548711337944940543))) (.node (.node (.leaf 431 5544662135879284957223684216941629861809407749541247793410607896911359232568277375930595780324921543731550456765631162719011862079) (.leaf 433 22137865358662827384011778049912605370210738739698448148994771988219209762976176703789768117499760787783075819681944980101270532095)) (.node (.leaf 439 1418215003326442557777578803765237018634549750056563872889687227406773199289111469732376077254825169153804741707174940037535720431592) (.leaf 443 22346135419111066841513158697972887567714515734033473996238498651436324301290265557893192769861155991400173046453165691533561935429627))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S5Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S5Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
