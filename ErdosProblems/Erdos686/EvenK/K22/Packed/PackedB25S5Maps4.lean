import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s5_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (80000000 + (r.val : ZMod 307)) + 25))) = true →
      (260674958303341327729697524514918144861254994861367499128502903346828667976485459653839289919).testBit r.val = true := by decide

theorem even22_b25_s5_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (80000000 + (i : ZMod 307)) + 25))) = true) :
    (260674958303341327729697524514918144861254994861367499128502903346828667976485459653839289919).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_307_fin r
  change even22A307
    (-(33 * (46 * (80000000 + ((i % 307 : ℕ) : ZMod 307)) + 25))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (80000000 + (r.val : ZMod 311)) + 25))) = true →
      (3128680373122714828041569122827119123265897096791913618088283430129742389479588611143719976895).testBit r.val = true := by decide

theorem even22_b25_s5_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (80000000 + (i : ZMod 311)) + 25))) = true) :
    (3128680373122714828041569122827119123265897096791913618088283430129742389479588611143719976895).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_311_fin r
  change even22A311
    (-(33 * (46 * (80000000 + ((i % 311 : ℕ) : ZMod 311)) + 25))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (80000000 + (r.val : ZMod 313)) + 25))) = true →
      (16654802163924866963037011274798880642992320511064985731596081103079839398827819675104386744191).testBit r.val = true := by decide

theorem even22_b25_s5_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (80000000 + (i : ZMod 313)) + 25))) = true) :
    (16654802163924866963037011274798880642992320511064985731596081103079839398827819675104386744191).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_313_fin r
  change even22A313
    (-(33 * (46 * (80000000 + ((i % 313 : ℕ) : ZMod 313)) + 25))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (80000000 + (r.val : ZMod 317)) + 25))) = true →
      (200248764720069533709087408801570493680819859289539923030304157290082855770106869160435116694526).testBit r.val = true := by decide

theorem even22_b25_s5_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (80000000 + (i : ZMod 317)) + 25))) = true) :
    (200248764720069533709087408801570493680819859289539923030304157290082855770106869160435116694526).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_317_fin r
  change even22A317
    (-(33 * (46 * (80000000 + ((i % 317 : ℕ) : ZMod 317)) + 25))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (80000000 + (r.val : ZMod 331)) + 25))) = true →
      (4374501449566014133471908005990874248278766698185191004127218857609296507552539743307673875868809983).testBit r.val = true := by decide

theorem even22_b25_s5_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (80000000 + (i : ZMod 331)) + 25))) = true) :
    (4374501449566014133471908005990874248278766698185191004127218857609296507552539743307673875868809983).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_331_fin r
  change even22A331
    (-(33 * (46 * (80000000 + ((i % 331 : ℕ) : ZMod 331)) + 25))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (80000000 + (r.val : ZMod 337)) + 25))) = true →
      (279831322848765907682838413381495710015614957318892908917281274734661239290837211102580458861572515695).testBit r.val = true := by decide

theorem even22_b25_s5_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (80000000 + (i : ZMod 337)) + 25))) = true) :
    (279831322848765907682838413381495710015614957318892908917281274734661239290837211102580458861572515695).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_337_fin r
  change even22A337
    (-(33 * (46 * (80000000 + ((i % 337 : ℕ) : ZMod 337)) + 25))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (80000000 + (r.val : ZMod 347)) + 25))) = true →
      (250850317498519087500834701723351985078947633379362379933427738085106740028985208316512779194615877074943).testBit r.val = true := by decide

theorem even22_b25_s5_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (80000000 + (i : ZMod 347)) + 25))) = true) :
    (250850317498519087500834701723351985078947633379362379933427738085106740028985208316512779194615877074943).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_347_fin r
  change even22A347
    (-(33 * (46 * (80000000 + ((i % 347 : ℕ) : ZMod 347)) + 25))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (80000000 + (r.val : ZMod 349)) + 25))) = true →
      (1146469062223816451232782475881176541222951235238180196647052518610374611783864725539579423716373516247037).testBit r.val = true := by decide

theorem even22_b25_s5_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (80000000 + (i : ZMod 349)) + 25))) = true) :
    (1146469062223816451232782475881176541222951235238180196647052518610374611783864725539579423716373516247037).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_349_fin r
  change even22A349
    (-(33 * (46 * (80000000 + ((i % 349 : ℕ) : ZMod 349)) + 25))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB25S5Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260674958303341327729697524514918144861254994861367499128502903346828667976485459653839289919) (.leaf 311 3128680373122714828041569122827119123265897096791913618088283430129742389479588611143719976895)) (.node (.leaf 313 16654802163924866963037011274798880642992320511064985731596081103079839398827819675104386744191) (.leaf 317 200248764720069533709087408801570493680819859289539923030304157290082855770106869160435116694526))) (.node (.node (.leaf 331 4374501449566014133471908005990874248278766698185191004127218857609296507552539743307673875868809983) (.leaf 337 279831322848765907682838413381495710015614957318892908917281274734661239290837211102580458861572515695)) (.node (.leaf 347 250850317498519087500834701723351985078947633379362379933427738085106740028985208316512779194615877074943) (.leaf 349 1146469062223816451232782475881176541222951235238180196647052518610374611783864725539579423716373516247037))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S5Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S5Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
