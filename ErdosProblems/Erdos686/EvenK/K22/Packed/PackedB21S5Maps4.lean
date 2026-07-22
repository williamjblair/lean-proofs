import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s5_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (80000000 + (r.val : ZMod 307)) + 21))) = true →
      (130233028644749939158162029998334598199541096189159472759480826838547145522252367020769116030).testBit r.val = true := by decide

theorem even22_b21_s5_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (80000000 + (i : ZMod 307)) + 21))) = true) :
    (130233028644749939158162029998334598199541096189159472759480826838547145522252367020769116030).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_307_fin r
  change even22A307
    (-(33 * (46 * (80000000 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (80000000 + (r.val : ZMod 311)) + 21))) = true →
      (3124813185754417884815115110678308009534600077028105030782418520461942644440752348910199963647).testBit r.val = true := by decide

theorem even22_b21_s5_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (80000000 + (i : ZMod 311)) + 21))) = true) :
    (3124813185754417884815115110678308009534600077028105030782418520461942644440752348910199963647).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_311_fin r
  change even22A311
    (-(33 * (46 * (80000000 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (80000000 + (r.val : ZMod 313)) + 21))) = true →
      (16685361433490363052530178319598566046976684751453986958606262393238530493582941976026098434047).testBit r.val = true := by decide

theorem even22_b21_s5_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (80000000 + (i : ZMod 313)) + 21))) = true) :
    (16685361433490363052530178319598566046976684751453986958606262393238530493582941976026098434047).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_313_fin r
  change even22A313
    (-(33 * (46 * (80000000 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (80000000 + (r.val : ZMod 317)) + 21))) = true →
      (266990040371900078742552929760196280299796483467070748837392095183566874013944017443055028142079).testBit r.val = true := by decide

theorem even22_b21_s5_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (80000000 + (i : ZMod 317)) + 21))) = true) :
    (266990040371900078742552929760196280299796483467070748837392095183566874013944017443055028142079).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_317_fin r
  change even22A317
    (-(33 * (46 * (80000000 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (80000000 + (r.val : ZMod 331)) + 21))) = true →
      (4374488868831833991426121358856428050028351440355815027897819942918168459263422655185627022811330554).testBit r.val = true := by decide

theorem even22_b21_s5_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (80000000 + (i : ZMod 331)) + 21))) = true) :
    (4374488868831833991426121358856428050028351440355815027897819942918168459263422655185627022811330554).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_331_fin r
  change even22A331
    (-(33 * (46 * (80000000 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (80000000 + (r.val : ZMod 337)) + 21))) = true →
      (262328776504869844844157229057252734860108352760723925414079983773802189554838858321232428849203969663).testBit r.val = true := by decide

theorem even22_b21_s5_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (80000000 + (i : ZMod 337)) + 21))) = true) :
    (262328776504869844844157229057252734860108352760723925414079983773802189554838858321232428849203969663).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_337_fin r
  change even22A337
    (-(33 * (46 * (80000000 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (80000000 + (r.val : ZMod 347)) + 21))) = true →
      (286686233340021749014479732337864950580450731587006006166645206154235773981901602125918693664524251168639).testBit r.val = true := by decide

theorem even22_b21_s5_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (80000000 + (i : ZMod 347)) + 21))) = true) :
    (286686233340021749014479732337864950580450731587006006166645206154235773981901602125918693664524251168639).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_347_fin r
  change even22A347
    (-(33 * (46 * (80000000 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (80000000 + (r.val : ZMod 349)) + 21))) = true →
      (1128262664860824002623597690258726100815267845365543206718219386627278958601561276253057048174605801226237).testBit r.val = true := by decide

theorem even22_b21_s5_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (80000000 + (i : ZMod 349)) + 21))) = true) :
    (1128262664860824002623597690258726100815267845365543206718219386627278958601561276253057048174605801226237).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_349_fin r
  change even22A349
    (-(33 * (46 * (80000000 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S5Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 130233028644749939158162029998334598199541096189159472759480826838547145522252367020769116030) (.leaf 311 3124813185754417884815115110678308009534600077028105030782418520461942644440752348910199963647)) (.node (.leaf 313 16685361433490363052530178319598566046976684751453986958606262393238530493582941976026098434047) (.leaf 317 266990040371900078742552929760196280299796483467070748837392095183566874013944017443055028142079))) (.node (.node (.leaf 331 4374488868831833991426121358856428050028351440355815027897819942918168459263422655185627022811330554) (.leaf 337 262328776504869844844157229057252734860108352760723925414079983773802189554838858321232428849203969663)) (.node (.leaf 347 286686233340021749014479732337864950580450731587006006166645206154235773981901602125918693664524251168639) (.leaf 349 1128262664860824002623597690258726100815267845365543206718219386627278958601561276253057048174605801226237))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S5Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S5Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
