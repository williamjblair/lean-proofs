import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s3_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (48000000 + (r.val : ZMod 499)) + 17))) = true →
      (630939306645686118408795713236608061654816436826505001413868580190297030536464771009010952725460159789951073112986707200634903685135509065363772932095).testBit r.val = true := by decide

theorem even22_b17_s3_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (48000000 + (i : ZMod 499)) + 17))) = true) :
    (630939306645686118408795713236608061654816436826505001413868580190297030536464771009010952725460159789951073112986707200634903685135509065363772932095).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_499_fin r
  change even22A499
    (-(33 * (46 * (48000000 + ((i % 499 : ℕ) : ZMod 499)) + 17))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (48000000 + (r.val : ZMod 503)) + 17))) = true →
      (26146367021051208044367635860104196743743842388516602181571027106367524187136467280825318228824026248330488297218922974194802063740513306715966717034367).testBit r.val = true := by decide

theorem even22_b17_s3_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (48000000 + (i : ZMod 503)) + 17))) = true) :
    (26146367021051208044367635860104196743743842388516602181571027106367524187136467280825318228824026248330488297218922974194802063740513306715966717034367).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_503_fin r
  change even22A503
    (-(33 * (46 * (48000000 + ((i % 503 : ℕ) : ZMod 503)) + 17))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (48000000 + (r.val : ZMod 509)) + 17))) = true →
      (828922231600767488859416004277464504729482355399169410725392709413261342667682143922093144430172762547199089713411107536521010550431253787356430419881470).testBit r.val = true := by decide

theorem even22_b17_s3_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (48000000 + (i : ZMod 509)) + 17))) = true) :
    (828922231600767488859416004277464504729482355399169410725392709413261342667682143922093144430172762547199089713411107536521010550431253787356430419881470).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_509_fin r
  change even22A509
    (-(33 * (46 * (48000000 + ((i % 509 : ℕ) : ZMod 509)) + 17))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (48000000 + (r.val : ZMod 521)) + 17))) = true →
      (6864741603316449064095253329107114070864266385648890390659862539358865153716238997518817557552265742924114404228058975995674492932751950432182964771125917183).testBit r.val = true := by decide

theorem even22_b17_s3_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (48000000 + (i : ZMod 521)) + 17))) = true) :
    (6864741603316449064095253329107114070864266385648890390659862539358865153716238997518817557552265742924114404228058975995674492932751950432182964771125917183).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_521_fin r
  change even22A521
    (-(33 * (46 * (48000000 + ((i % 521 : ℕ) : ZMod 521)) + 17))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (48000000 + (r.val : ZMod 523)) + 17))) = true →
      (27023436064051678446949020504073150423378424603236702433303057262854155996552315700092891930871161536786562911345557028555441459833077124521699656034795913210).testBit r.val = true := by decide

theorem even22_b17_s3_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (48000000 + (i : ZMod 523)) + 17))) = true) :
    (27023436064051678446949020504073150423378424603236702433303057262854155996552315700092891930871161536786562911345557028555441459833077124521699656034795913210).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_523_fin r
  change even22A523
    (-(33 * (46 * (48000000 + ((i % 523 : ℕ) : ZMod 523)) + 17))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (48000000 + (r.val : ZMod 541)) + 17))) = true →
      (7028508496313556854075169382900298232076348206702992783096209055077240838863578685975930611882782587438630797491093363733633120565386588964579802764151413437624253).testBit r.val = true := by decide

theorem even22_b17_s3_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (48000000 + (i : ZMod 541)) + 17))) = true) :
    (7028508496313556854075169382900298232076348206702992783096209055077240838863578685975930611882782587438630797491093363733633120565386588964579802764151413437624253).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_541_fin r
  change even22A541
    (-(33 * (46 * (48000000 + ((i % 541 : ℕ) : ZMod 541)) + 17))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (48000000 + (r.val : ZMod 547)) + 17))) = true →
      (451239296096668648084083043584857044188041912148164539843822011339342899307735867428681266485189815734830489813730739393801227260138247932910692390233546000099704818).testBit r.val = true := by decide

theorem even22_b17_s3_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (48000000 + (i : ZMod 547)) + 17))) = true) :
    (451239296096668648084083043584857044188041912148164539843822011339342899307735867428681266485189815734830489813730739393801227260138247932910692390233546000099704818).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_547_fin r
  change even22A547
    (-(33 * (46 * (48000000 + ((i % 547 : ℕ) : ZMod 547)) + 17))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b17_s3_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (48000000 + (r.val : ZMod 557)) + 17))) = true →
      (463445648940591422281255073779227238143549430694390561969801214326021778817924783480770835940382162405444248715450345208941661724788170790315554153661880281968640782782).testBit r.val = true := by decide

theorem even22_b17_s3_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (48000000 + (i : ZMod 557)) + 17))) = true) :
    (463445648940591422281255073779227238143549430694390561969801214326021778817924783480770835940382162405444248715450345208941661724788170790315554153661880281968640782782).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s3_map_557_fin r
  change even22A557
    (-(33 * (46 * (48000000 + ((i % 557 : ℕ) : ZMod 557)) + 17))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB17S3Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 630939306645686118408795713236608061654816436826505001413868580190297030536464771009010952725460159789951073112986707200634903685135509065363772932095) (.leaf 503 26146367021051208044367635860104196743743842388516602181571027106367524187136467280825318228824026248330488297218922974194802063740513306715966717034367)) (.node (.leaf 509 828922231600767488859416004277464504729482355399169410725392709413261342667682143922093144430172762547199089713411107536521010550431253787356430419881470) (.leaf 521 6864741603316449064095253329107114070864266385648890390659862539358865153716238997518817557552265742924114404228058975995674492932751950432182964771125917183))) (.node (.node (.leaf 523 27023436064051678446949020504073150423378424603236702433303057262854155996552315700092891930871161536786562911345557028555441459833077124521699656034795913210) (.leaf 541 7028508496313556854075169382900298232076348206702992783096209055077240838863578685975930611882782587438630797491093363733633120565386588964579802764151413437624253)) (.node (.leaf 547 451239296096668648084083043584857044188041912148164539843822011339342899307735867428681266485189815734830489813730739393801227260138247932910692390233546000099704818) (.leaf 557 463445648940591422281255073779227238143549430694390561969801214326021778817924783480770835940382162405444248715450345208941661724788170790315554153661880281968640782782))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S3Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S3Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s3_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
