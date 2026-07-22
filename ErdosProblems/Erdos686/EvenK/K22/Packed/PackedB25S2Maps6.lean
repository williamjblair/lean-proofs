import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s2_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (32000000 + (r.val : ZMod 401)) + 25))) = true →
      (5164498519976154960853623560074009961383259907173534896322978773424429521593625973239785978979987625383564404170589989887).testBit r.val = true := by decide

theorem even22_b25_s2_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (32000000 + (i : ZMod 401)) + 25))) = true) :
    (5164498519976154960853623560074009961383259907173534896322978773424429521593625973239785978979987625383564404170589989887).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_401_fin r
  change even22A401
    (-(33 * (46 * (32000000 + ((i % 401 : ℕ) : ZMod 401)) + 25))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (32000000 + (r.val : ZMod 409)) + 25))) = true →
      (1156847861653633239891229430489871721128136048690350344225972951394666323519738774572568373511804328307050326730019212034015).testBit r.val = true := by decide

theorem even22_b25_s2_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (32000000 + (i : ZMod 409)) + 25))) = true) :
    (1156847861653633239891229430489871721128136048690350344225972951394666323519738774572568373511804328307050326730019212034015).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_409_fin r
  change even22A409
    (-(33 * (46 * (32000000 + ((i % 409 : ℕ) : ZMod 409)) + 25))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (32000000 + (r.val : ZMod 419)) + 25))) = true →
      (1342587159839709184523523362117285689486940098556783804854058436310203744781137579850527190488255284322351182803686628986715895).testBit r.val = true := by decide

theorem even22_b25_s2_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (32000000 + (i : ZMod 419)) + 25))) = true) :
    (1342587159839709184523523362117285689486940098556783804854058436310203744781137579850527190488255284322351182803686628986715895).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_419_fin r
  change even22A419
    (-(33 * (46 * (32000000 + ((i % 419 : ℕ) : ZMod 419)) + 25))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (32000000 + (r.val : ZMod 421)) + 25))) = true →
      (3674802383636799776638102695257530617987653519169975229127979698039445447080152434766052087883704802111415631425842454404792318).testBit r.val = true := by decide

theorem even22_b25_s2_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (32000000 + (i : ZMod 421)) + 25))) = true) :
    (3674802383636799776638102695257530617987653519169975229127979698039445447080152434766052087883704802111415631425842454404792318).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_421_fin r
  change even22A421
    (-(33 * (46 * (32000000 + ((i % 421 : ℕ) : ZMod 421)) + 25))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (32000000 + (r.val : ZMod 431)) + 25))) = true →
      (5415364543919705394682943539711700073817049487231851327500019443393816244541325387892956754623499609961237083852767215705160940535).testBit r.val = true := by decide

theorem even22_b25_s2_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (32000000 + (i : ZMod 431)) + 25))) = true) :
    (5415364543919705394682943539711700073817049487231851327500019443393816244541325387892956754623499609961237083852767215705160940535).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_431_fin r
  change even22A431
    (-(33 * (46 * (32000000 + ((i % 431 : ℕ) : ZMod 431)) + 25))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (32000000 + (r.val : ZMod 433)) + 25))) = true →
      (21834773830872417506520020586455749226465378960075704554974766307570939800064706396103411273452828955977326755443341274648414257147).testBit r.val = true := by decide

theorem even22_b25_s2_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (32000000 + (i : ZMod 433)) + 25))) = true) :
    (21834773830872417506520020586455749226465378960075704554974766307570939800064706396103411273452828955977326755443341274648414257147).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_433_fin r
  change even22A433
    (-(33 * (46 * (32000000 + ((i % 433 : ℕ) : ZMod 433)) + 25))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (32000000 + (r.val : ZMod 439)) + 25))) = true →
      (709754703359169445115456070849129825507833066382581148015101190437578303005714736172726377483824970651866193741715256321784705712124).testBit r.val = true := by decide

theorem even22_b25_s2_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (32000000 + (i : ZMod 439)) + 25))) = true) :
    (709754703359169445115456070849129825507833066382581148015101190437578303005714736172726377483824970651866193741715256321784705712124).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_439_fin r
  change even22A439
    (-(33 * (46 * (32000000 + ((i % 439 : ℕ) : ZMod 439)) + 25))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b25_s2_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (32000000 + (r.val : ZMod 443)) + 25))) = true →
      (22713666300204367074955589017845843758187747865118757494990428291697128115153434064343158889265758270452170882956868977339036912779007).testBit r.val = true := by decide

theorem even22_b25_s2_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (32000000 + (i : ZMod 443)) + 25))) = true) :
    (22713666300204367074955589017845843758187747865118757494990428291697128115153434064343158889265758270452170882956868977339036912779007).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s2_map_443_fin r
  change even22A443
    (-(33 * (46 * (32000000 + ((i % 443 : ℕ) : ZMod 443)) + 25))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB25S2Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5164498519976154960853623560074009961383259907173534896322978773424429521593625973239785978979987625383564404170589989887) (.leaf 409 1156847861653633239891229430489871721128136048690350344225972951394666323519738774572568373511804328307050326730019212034015)) (.node (.leaf 419 1342587159839709184523523362117285689486940098556783804854058436310203744781137579850527190488255284322351182803686628986715895) (.leaf 421 3674802383636799776638102695257530617987653519169975229127979698039445447080152434766052087883704802111415631425842454404792318))) (.node (.node (.leaf 431 5415364543919705394682943539711700073817049487231851327500019443393816244541325387892956754623499609961237083852767215705160940535) (.leaf 433 21834773830872417506520020586455749226465378960075704554974766307570939800064706396103411273452828955977326755443341274648414257147)) (.node (.leaf 439 709754703359169445115456070849129825507833066382581148015101190437578303005714736172726377483824970651866193741715256321784705712124) (.leaf 443 22713666300204367074955589017845843758187747865118757494990428291697128115153434064343158889265758270452170882956868977339036912779007))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S2Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S2Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s2_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
