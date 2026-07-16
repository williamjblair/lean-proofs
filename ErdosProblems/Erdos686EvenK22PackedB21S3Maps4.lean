import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (48000000 + (r.val : ZMod 307)) + 21))) = true →
      (260739579241431624403434322613783135291928566407444342948254716751869172360081719294145593055).testBit r.val = true := by decide

theorem even22_b21_s3_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (48000000 + (i : ZMod 307)) + 21))) = true) :
    (260739579241431624403434322613783135291928566407444342948254716751869172360081719294145593055).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_307_fin r
  change even22A307
    (-(33 * (46 * (48000000 + ((i % 307 : ℕ) : ZMod 307)) + 21))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (48000000 + (r.val : ZMod 311)) + 21))) = true →
      (3096278769623908192761597338881081682835607379025620036358040263646041193079907230178992979967).testBit r.val = true := by decide

theorem even22_b21_s3_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (48000000 + (i : ZMod 311)) + 21))) = true) :
    (3096278769623908192761597338881081682835607379025620036358040263646041193079907230178992979967).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_311_fin r
  change even22A311
    (-(33 * (46 * (48000000 + ((i % 311 : ℕ) : ZMod 311)) + 21))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (48000000 + (r.val : ZMod 313)) + 21))) = true →
      (16685361433494157327731476091658954317062297295295952013110313719984138344609164633182516019191).testBit r.val = true := by decide

theorem even22_b21_s3_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (48000000 + (i : ZMod 313)) + 21))) = true) :
    (16685361433494157327731476091658954317062297295295952013110313719984138344609164633182516019191).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_313_fin r
  change even22A313
    (-(33 * (46 * (48000000 + ((i % 313 : ℕ) : ZMod 313)) + 21))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (48000000 + (r.val : ZMod 317)) + 21))) = true →
      (130333380205916764281689838201468808596553308753616660288759255460780836901411160064167235289087).testBit r.val = true := by decide

theorem even22_b21_s3_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (48000000 + (i : ZMod 317)) + 21))) = true) :
    (130333380205916764281689838201468808596553308753616660288759255460780836901411160064167235289087).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_317_fin r
  change even22A317
    (-(33 * (46 * (48000000 + ((i % 317 : ℕ) : ZMod 317)) + 21))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (48000000 + (r.val : ZMod 331)) + 21))) = true →
      (4096555807752273564138426110448097817398703341660587419113248652278406876427966039568638931894271679).testBit r.val = true := by decide

theorem even22_b21_s3_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (48000000 + (i : ZMod 331)) + 21))) = true) :
    (4096555807752273564138426110448097817398703341660587419113248652278406876427966039568638931894271679).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_331_fin r
  change even22A331
    (-(33 * (46 * (48000000 + ((i % 331 : ℕ) : ZMod 331)) + 21))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (48000000 + (r.val : ZMod 337)) + 21))) = true →
      (253446596669996579789556731210134776026193874716368888317780094009170825960292935251820276995690855865).testBit r.val = true := by decide

theorem even22_b21_s3_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (48000000 + (i : ZMod 337)) + 21))) = true) :
    (253446596669996579789556731210134776026193874716368888317780094009170825960292935251820276995690855865).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_337_fin r
  change even22A337
    (-(33 * (46 * (48000000 + ((i % 337 : ℕ) : ZMod 337)) + 21))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (48000000 + (r.val : ZMod 347)) + 21))) = true →
      (286547338680398627031624026326083489152224440090305949996363562474778411778708744006048258435858875531263).testBit r.val = true := by decide

theorem even22_b21_s3_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (48000000 + (i : ZMod 347)) + 21))) = true) :
    (286547338680398627031624026326083489152224440090305949996363562474778411778708744006048258435858875531263).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_347_fin r
  change even22A347
    (-(33 * (46 * (48000000 + ((i % 347 : ℕ) : ZMod 347)) + 21))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (48000000 + (r.val : ZMod 349)) + 21))) = true →
      (1075006390562893785212649674565109601513480102018287065102867742423233915387556709204966949850595123527167).testBit r.val = true := by decide

theorem even22_b21_s3_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (48000000 + (i : ZMod 349)) + 21))) = true) :
    (1075006390562893785212649674565109601513480102018287065102867742423233915387556709204966949850595123527167).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_349_fin r
  change even22A349
    (-(33 * (46 * (48000000 + ((i % 349 : ℕ) : ZMod 349)) + 21))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260739579241431624403434322613783135291928566407444342948254716751869172360081719294145593055) (.leaf 311 3096278769623908192761597338881081682835607379025620036358040263646041193079907230178992979967)) (.node (.leaf 313 16685361433494157327731476091658954317062297295295952013110313719984138344609164633182516019191) (.leaf 317 130333380205916764281689838201468808596553308753616660288759255460780836901411160064167235289087))) (.node (.node (.leaf 331 4096555807752273564138426110448097817398703341660587419113248652278406876427966039568638931894271679) (.leaf 337 253446596669996579789556731210134776026193874716368888317780094009170825960292935251820276995690855865)) (.node (.leaf 347 286547338680398627031624026326083489152224440090305949996363562474778411778708744006048258435858875531263) (.leaf 349 1075006390562893785212649674565109601513480102018287065102867742423233915387556709204966949850595123527167))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
