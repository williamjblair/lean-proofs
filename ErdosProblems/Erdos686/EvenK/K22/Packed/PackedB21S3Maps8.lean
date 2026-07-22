import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s3_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (48000000 + (r.val : ZMod 499)) + 21))) = true →
      (1499588107617423469727550034290324600088959247087675009082820249903874524662211031691137209420917295134377368982665406460745444867781620072399849388983).testBit r.val = true := by decide

theorem even22_b21_s3_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (48000000 + (i : ZMod 499)) + 21))) = true) :
    (1499588107617423469727550034290324600088959247087675009082820249903874524662211031691137209420917295134377368982665406460745444867781620072399849388983).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_499_fin r
  change even22A499
    (-(33 * (46 * (48000000 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (48000000 + (r.val : ZMod 503)) + 21))) = true →
      (19578807712515778854353783207167107956210046384472419059725627789635167880867358678788942700559661984678202913714889558128407397247016670276617180540863).testBit r.val = true := by decide

theorem even22_b21_s3_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (48000000 + (i : ZMod 503)) + 21))) = true) :
    (19578807712515778854353783207167107956210046384472419059725627789635167880867358678788942700559661984678202913714889558128407397247016670276617180540863).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_503_fin r
  change even22A503
    (-(33 * (46 * (48000000 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (48000000 + (r.val : ZMod 509)) + 21))) = true →
      (1359228898180699048264538873136413912027448437334918934384908337181342825603078712318777563959715304186085751483190768215118909005419541573932100310003707).testBit r.val = true := by decide

theorem even22_b21_s3_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (48000000 + (i : ZMod 509)) + 21))) = true) :
    (1359228898180699048264538873136413912027448437334918934384908337181342825603078712318777563959715304186085751483190768215118909005419541573932100310003707).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_509_fin r
  change even22A509
    (-(33 * (46 * (48000000 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (48000000 + (r.val : ZMod 521)) + 21))) = true →
      (6864797449000121124224865634301461061775795065140642106340155462154661912975194744637680735165300223418028837492612445473531048427514352758496620325315010557).testBit r.val = true := by decide

theorem even22_b21_s3_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (48000000 + (i : ZMod 521)) + 21))) = true) :
    (6864797449000121124224865634301461061775795065140642106340155462154661912975194744637680735165300223418028837492612445473531048427514352758496620325315010557).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_521_fin r
  change even22A521
    (-(33 * (46 * (48000000 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (48000000 + (r.val : ZMod 523)) + 21))) = true →
      (27442299944934966245358975694919770018082995975045125750787532863380226410892313451456748714276915073604907033021395403598961011387323581037954373183780929279).testBit r.val = true := by decide

theorem even22_b21_s3_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (48000000 + (i : ZMod 523)) + 21))) = true) :
    (27442299944934966245358975694919770018082995975045125750787532863380226410892313451456748714276915073604907033021395403598961011387323581037954373183780929279).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_523_fin r
  change even22A523
    (-(33 * (46 * (48000000 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (48000000 + (r.val : ZMod 541)) + 21))) = true →
      (7178810552873957687270843227800329996249669843530905996239875736949115521102317492995330967401174851223858197996841521067720147917499652756162277760621708162497495).testBit r.val = true := by decide

theorem even22_b21_s3_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (48000000 + (i : ZMod 541)) + 21))) = true) :
    (7178810552873957687270843227800329996249669843530905996239875736949115521102317492995330967401174851223858197996841521067720147917499652756162277760621708162497495).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_541_fin r
  change even22A541
    (-(33 * (46 * (48000000 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (48000000 + (r.val : ZMod 547)) + 21))) = true →
      (431894731454713238570337433852788722662345928629319876233969272005657062518851279422123413322490568876278729294622645582982721235965255769331452809443955801887604733).testBit r.val = true := by decide

theorem even22_b21_s3_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (48000000 + (i : ZMod 547)) + 21))) = true) :
    (431894731454713238570337433852788722662345928629319876233969272005657062518851279422123413322490568876278729294622645582982721235965255769331452809443955801887604733).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_547_fin r
  change even22A547
    (-(33 * (46 * (48000000 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s3_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (48000000 + (r.val : ZMod 557)) + 21))) = true →
      (344580749101446307485496501592158835045898654268690343464845805566820741700340735199559602649713649835776862709258680790070839544544820264142249380074270780923018476281).testBit r.val = true := by decide

theorem even22_b21_s3_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (48000000 + (i : ZMod 557)) + 21))) = true) :
    (344580749101446307485496501592158835045898654268690343464845805566820741700340735199559602649713649835776862709258680790070839544544820264142249380074270780923018476281).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s3_map_557_fin r
  change even22A557
    (-(33 * (46 * (48000000 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S3Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1499588107617423469727550034290324600088959247087675009082820249903874524662211031691137209420917295134377368982665406460745444867781620072399849388983) (.leaf 503 19578807712515778854353783207167107956210046384472419059725627789635167880867358678788942700559661984678202913714889558128407397247016670276617180540863)) (.node (.leaf 509 1359228898180699048264538873136413912027448437334918934384908337181342825603078712318777563959715304186085751483190768215118909005419541573932100310003707) (.leaf 521 6864797449000121124224865634301461061775795065140642106340155462154661912975194744637680735165300223418028837492612445473531048427514352758496620325315010557))) (.node (.node (.leaf 523 27442299944934966245358975694919770018082995975045125750787532863380226410892313451456748714276915073604907033021395403598961011387323581037954373183780929279) (.leaf 541 7178810552873957687270843227800329996249669843530905996239875736949115521102317492995330967401174851223858197996841521067720147917499652756162277760621708162497495)) (.node (.leaf 547 431894731454713238570337433852788722662345928629319876233969272005657062518851279422123413322490568876278729294622645582982721235965255769331452809443955801887604733) (.leaf 557 344580749101446307485496501592158835045898654268690343464845805566820741700340735199559602649713649835776862709258680790070839544544820264142249380074270780923018476281))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S3Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S3Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s3_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
