import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s3_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (48000000 + (r.val : ZMod 499)) + 29))) = true →
      (715629418057359092104376407737998259423424066805710241461487912868687727656142832161438737963964652515759614269378009021345834383433796817364107394779).testBit r.val = true := by decide

theorem even22_b29_s3_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (48000000 + (i : ZMod 499)) + 29))) = true) :
    (715629418057359092104376407737998259423424066805710241461487912868687727656142832161438737963964652515759614269378009021345834383433796817364107394779).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_499_fin r
  change even22A499
    (-(33 * (46 * (48000000 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (48000000 + (r.val : ZMod 503)) + 29))) = true →
      (26186125903442495115234636518788968820124114076372965520166723908257123844432613700943980167664882459998787584617275166459508474274913374236729086572031).testBit r.val = true := by decide

theorem even22_b29_s3_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (48000000 + (i : ZMod 503)) + 29))) = true) :
    (26186125903442495115234636518788968820124114076372965520166723908257123844432613700943980167664882459998787584617275166459508474274913374236729086572031).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_503_fin r
  change even22A503
    (-(33 * (46 * (48000000 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (48000000 + (r.val : ZMod 509)) + 29))) = true →
      (1437018270827113756625061307267783268680710791991242716569767751416798790463736075640029253088462937297105493443518043159274382041706009053612571491235839).testBit r.val = true := by decide

theorem even22_b29_s3_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (48000000 + (i : ZMod 509)) + 29))) = true) :
    (1437018270827113756625061307267783268680710791991242716569767751416798790463736075640029253088462937297105493443518043159274382041706009053612571491235839).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_509_fin r
  change even22A509
    (-(33 * (46 * (48000000 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (48000000 + (r.val : ZMod 521)) + 29))) = true →
      (6006697936527423917355059954953314956331914875147635110753007286079700023233205206963492197693340449372427238454493683765755018212699117816791306674989170669).testBit r.val = true := by decide

theorem even22_b29_s3_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (48000000 + (i : ZMod 521)) + 29))) = true) :
    (6006697936527423917355059954953314956331914875147635110753007286079700023233205206963492197693340449372427238454493683765755018212699117816791306674989170669).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_521_fin r
  change even22A521
    (-(33 * (46 * (48000000 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (48000000 + (r.val : ZMod 523)) + 29))) = true →
      (26601074514107079685264587088182690896946213958233888721367130784688161182692693874406202695633595169888531505927333158031411845787318361336290284740196368127).testBit r.val = true := by decide

theorem even22_b29_s3_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (48000000 + (i : ZMod 523)) + 29))) = true) :
    (26601074514107079685264587088182690896946213958233888721367130784688161182692693874406202695633595169888531505927333158031411845787318361336290284740196368127).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_523_fin r
  change even22A523
    (-(33 * (46 * (48000000 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (48000000 + (r.val : ZMod 541)) + 29))) = true →
      (2670982718183960838618468937029606228710107564918649119910909315028558371242947116590692278435511587659997791832516800273535538339493554116207203900370778649761791).testBit r.val = true := by decide

theorem even22_b29_s3_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (48000000 + (i : ZMod 541)) + 29))) = true) :
    (2670982718183960838618468937029606228710107564918649119910909315028558371242947116590692278435511587659997791832516800273535538339493554116207203900370778649761791).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_541_fin r
  change even22A541
    (-(33 * (46 * (48000000 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (48000000 + (r.val : ZMod 547)) + 29))) = true →
      (446264115566103645213596129050835505230360839426159385438643694527080690301405838985702714886113080719270148969722736935838702249726382475989645775601392270269480959).testBit r.val = true := by decide

theorem even22_b29_s3_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (48000000 + (i : ZMod 547)) + 29))) = true) :
    (446264115566103645213596129050835505230360839426159385438643694527080690301405838985702714886113080719270148969722736935838702249726382475989645775601392270269480959).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_547_fin r
  change even22A547
    (-(33 * (46 * (48000000 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s3_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (48000000 + (r.val : ZMod 557)) + 29))) = true →
      (449632242002484690282222316009842774852334324489629636260518457743463677433918435413730549475608006831218681415672913510037009356025490314097905032742401544276771077835).testBit r.val = true := by decide

theorem even22_b29_s3_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (48000000 + (i : ZMod 557)) + 29))) = true) :
    (449632242002484690282222316009842774852334324489629636260518457743463677433918435413730549475608006831218681415672913510037009356025490314097905032742401544276771077835).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s3_map_557_fin r
  change even22A557
    (-(33 * (46 * (48000000 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S3Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 715629418057359092104376407737998259423424066805710241461487912868687727656142832161438737963964652515759614269378009021345834383433796817364107394779) (.leaf 503 26186125903442495115234636518788968820124114076372965520166723908257123844432613700943980167664882459998787584617275166459508474274913374236729086572031)) (.node (.leaf 509 1437018270827113756625061307267783268680710791991242716569767751416798790463736075640029253088462937297105493443518043159274382041706009053612571491235839) (.leaf 521 6006697936527423917355059954953314956331914875147635110753007286079700023233205206963492197693340449372427238454493683765755018212699117816791306674989170669))) (.node (.node (.leaf 523 26601074514107079685264587088182690896946213958233888721367130784688161182692693874406202695633595169888531505927333158031411845787318361336290284740196368127) (.leaf 541 2670982718183960838618468937029606228710107564918649119910909315028558371242947116590692278435511587659997791832516800273535538339493554116207203900370778649761791)) (.node (.leaf 547 446264115566103645213596129050835505230360839426159385438643694527080690301405838985702714886113080719270148969722736935838702249726382475989645775601392270269480959) (.leaf 557 449632242002484690282222316009842774852334324489629636260518457743463677433918435413730549475608006831218681415672913510037009356025490314097905032742401544276771077835))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S3Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S3Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s3_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
