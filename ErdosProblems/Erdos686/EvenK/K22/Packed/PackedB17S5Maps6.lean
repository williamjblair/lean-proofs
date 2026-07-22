import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s5_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (80000000 + (r.val : ZMod 401)) + 17))) = true →
      (5144245893676029959920818401892133016190311288858119946299747374993298786149362325693834031121069455515865071902026366975).testBit r.val = true := by decide

theorem even22_b17_s5_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (80000000 + (i : ZMod 401)) + 17))) = true) :
    (5144245893676029959920818401892133016190311288858119946299747374993298786149362325693834031121069455515865071902026366975).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_401_fin r
  change even22A401
    (-(33 * (46 * (80000000 + ((i % 401 : ℕ) : ZMod 401)) + 17))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (80000000 + (r.val : ZMod 409)) + 17))) = true →
      (1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263).testBit r.val = true := by decide

theorem even22_b17_s5_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (80000000 + (i : ZMod 409)) + 17))) = true) :
    (1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_409_fin r
  change even22A409
    (-(33 * (46 * (80000000 + ((i % 409 : ℕ) : ZMod 409)) + 17))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (80000000 + (r.val : ZMod 419)) + 17))) = true →
      (1351838394700490238508122892311032438574305497138018976818171700489806123206922060296278475444713193010937659945679659226856703).testBit r.val = true := by decide

theorem even22_b17_s5_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (80000000 + (i : ZMod 419)) + 17))) = true) :
    (1351838394700490238508122892311032438574305497138018976818171700489806123206922060296278475444713193010937659945679659226856703).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_419_fin r
  change even22A419
    (-(33 * (46 * (80000000 + ((i % 419 : ℕ) : ZMod 419)) + 17))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (80000000 + (r.val : ZMod 421)) + 17))) = true →
      (4643133174891631200068741090075886305059544678285686182249245859751804735203813506257333286917800699067978013723565758192025578).testBit r.val = true := by decide

theorem even22_b17_s5_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (80000000 + (i : ZMod 421)) + 17))) = true) :
    (4643133174891631200068741090075886305059544678285686182249245859751804735203813506257333286917800699067978013723565758192025578).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_421_fin r
  change even22A421
    (-(33 * (46 * (80000000 + ((i % 421 : ℕ) : ZMod 421)) + 17))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (80000000 + (r.val : ZMod 431)) + 17))) = true →
      (5371773686695387340913023813700455212064262008338140472158678785457641180046898131194292731742222029700309099501769824651272257471).testBit r.val = true := by decide

theorem even22_b17_s5_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (80000000 + (i : ZMod 431)) + 17))) = true) :
    (5371773686695387340913023813700455212064262008338140472158678785457641180046898131194292731742222029700309099501769824651272257471).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_431_fin r
  change even22A431
    (-(33 * (46 * (80000000 + ((i % 431 : ℕ) : ZMod 431)) + 17))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (80000000 + (r.val : ZMod 433)) + 17))) = true →
      (22181267308012297525896782659417534443574089756834957962720712626619392141229579817653125090313669169231754694642561859018431657975).testBit r.val = true := by decide

theorem even22_b17_s5_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (80000000 + (i : ZMod 433)) + 17))) = true) :
    (22181267308012297525896782659417534443574089756834957962720712626619392141229579817653125090313669169231754694642561859018431657975).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_433_fin r
  change even22A433
    (-(33 * (46 * (80000000 + ((i % 433 : ℕ) : ZMod 433)) + 17))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (80000000 + (r.val : ZMod 439)) + 17))) = true →
      (1408494542965075372018015255476092965124257142821873143023060154707725731281851841204545863716324051239929081660401051647624343452671).testBit r.val = true := by decide

theorem even22_b17_s5_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (80000000 + (i : ZMod 439)) + 17))) = true) :
    (1408494542965075372018015255476092965124257142821873143023060154707725731281851841204545863716324051239929081660401051647624343452671).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_439_fin r
  change even22A439
    (-(33 * (46 * (80000000 + ((i % 439 : ℕ) : ZMod 439)) + 17))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (80000000 + (r.val : ZMod 443)) + 17))) = true →
      (22713536141288702425480488681317866827066679022892276267393136365948912730952158255799011899443432033055125589420529429127541221358591).testBit r.val = true := by decide

theorem even22_b17_s5_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (80000000 + (i : ZMod 443)) + 17))) = true) :
    (22713536141288702425480488681317866827066679022892276267393136365948912730952158255799011899443432033055125589420529429127541221358591).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_443_fin r
  change even22A443
    (-(33 * (46 * (80000000 + ((i % 443 : ℕ) : ZMod 443)) + 17))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB17S5Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5144245893676029959920818401892133016190311288858119946299747374993298786149362325693834031121069455515865071902026366975) (.leaf 409 1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263)) (.node (.leaf 419 1351838394700490238508122892311032438574305497138018976818171700489806123206922060296278475444713193010937659945679659226856703) (.leaf 421 4643133174891631200068741090075886305059544678285686182249245859751804735203813506257333286917800699067978013723565758192025578))) (.node (.node (.leaf 431 5371773686695387340913023813700455212064262008338140472158678785457641180046898131194292731742222029700309099501769824651272257471) (.leaf 433 22181267308012297525896782659417534443574089756834957962720712626619392141229579817653125090313669169231754694642561859018431657975)) (.node (.leaf 439 1408494542965075372018015255476092965124257142821873143023060154707725731281851841204545863716324051239929081660401051647624343452671) (.leaf 443 22713536141288702425480488681317866827066679022892276267393136365948912730952158255799011899443432033055125589420529429127541221358591))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S5Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S5Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
