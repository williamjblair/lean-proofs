import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s3_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (48000000 + (r.val : ZMod 499)) + 25))) = true →
      (537040646296850529732463374265597906164432131094492051994220763125979316032501235619259383159487519824528224601065193804011920523620448034792934963194).testBit r.val = true := by decide

theorem even22_b25_s3_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (48000000 + (i : ZMod 499)) + 25))) = true) :
    (537040646296850529732463374265597906164432131094492051994220763125979316032501235619259383159487519824528224601065193804011920523620448034792934963194).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_499_fin r
  change even22A499
    (-(33 * (46 * (48000000 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (48000000 + (r.val : ZMod 503)) + 25))) = true →
      (13093362623672285846650765002331207264142156196015120978133517598074940955429947523882731138704366147976518887489650585153852906590069281430595256047582).testBit r.val = true := by decide

theorem even22_b25_s3_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (48000000 + (i : ZMod 503)) + 25))) = true) :
    (13093362623672285846650765002331207264142156196015120978133517598074940955429947523882731138704366147976518887489650585153852906590069281430595256047582).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_503_fin r
  change even22A503
    (-(33 * (46 * (48000000 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (48000000 + (r.val : ZMod 509)) + 25))) = true →
      (1557796480597028573509108259777629462406315629759633602521115150405337202372584340439034833221114403594442233918266196154388679017812693094048224675614710).testBit r.val = true := by decide

theorem even22_b25_s3_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (48000000 + (i : ZMod 509)) + 25))) = true) :
    (1557796480597028573509108259777629462406315629759633602521115150405337202372584340439034833221114403594442233918266196154388679017812693094048224675614710).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_509_fin r
  change even22A509
    (-(33 * (46 * (48000000 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (48000000 + (r.val : ZMod 521)) + 25))) = true →
      (6864794385913860325250622936435903531989770885575027517674172172221201517487807587909766930328929332927715851058641350228839455259633323986656891203940580319).testBit r.val = true := by decide

theorem even22_b25_s3_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (48000000 + (i : ZMod 521)) + 25))) = true) :
    (6864794385913860325250622936435903531989770885575027517674172172221201517487807587909766930328929332927715851058641350228839455259633323986656891203940580319).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_521_fin r
  change even22A521
    (-(33 * (46 * (48000000 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (48000000 + (r.val : ZMod 523)) + 25))) = true →
      (27030087578183496079519346090299653240693780933434041199266930211598172948499206671703487154346035874966031271295483032327009890092775786129834589183776096223).testBit r.val = true := by decide

theorem even22_b25_s3_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (48000000 + (i : ZMod 523)) + 25))) = true) :
    (27030087578183496079519346090299653240693780933434041199266930211598172948499206671703487154346035874966031271295483032327009890092775786129834589183776096223).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_523_fin r
  change even22A523
    (-(33 * (46 * (48000000 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (48000000 + (r.val : ZMod 541)) + 25))) = true →
      (7198031242393724183618360480730994613839291367014779162932610646651620933790129713498660250417370701639977798796675371270252947542641429600414883857139610530217983).testBit r.val = true := by decide

theorem even22_b25_s3_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (48000000 + (i : ZMod 541)) + 25))) = true) :
    (7198031242393724183618360480730994613839291367014779162932610646651620933790129713498660250417370701639977798796675371270252947542641429600414883857139610530217983).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_541_fin r
  change even22A541
    (-(33 * (46 * (48000000 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (48000000 + (r.val : ZMod 547)) + 25))) = true →
      (460628499636929298117471584689969500854276113430914683391169944199882114195967322163548485582281424243839679724797328371462479773438341114854306146976999613152624637).testBit r.val = true := by decide

theorem even22_b25_s3_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (48000000 + (i : ZMod 547)) + 25))) = true) :
    (460628499636929298117471584689969500854276113430914683391169944199882114195967322163548485582281424243839679724797328371462479773438341114854306146976999613152624637).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_547_fin r
  change even22A547
    (-(33 * (46 * (48000000 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s3_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (48000000 + (r.val : ZMod 557)) + 25))) = true →
      (353456262032342462739811796020304034916498756017088906418554406409752562960620064496923072691351893205713678447241388928294292321470843569333852344215494636527320825339).testBit r.val = true := by decide

theorem even22_b25_s3_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (48000000 + (i : ZMod 557)) + 25))) = true) :
    (353456262032342462739811796020304034916498756017088906418554406409752562960620064496923072691351893205713678447241388928294292321470843569333852344215494636527320825339).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s3_map_557_fin r
  change even22A557
    (-(33 * (46 * (48000000 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S3Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 537040646296850529732463374265597906164432131094492051994220763125979316032501235619259383159487519824528224601065193804011920523620448034792934963194) (.leaf 503 13093362623672285846650765002331207264142156196015120978133517598074940955429947523882731138704366147976518887489650585153852906590069281430595256047582)) (.node (.leaf 509 1557796480597028573509108259777629462406315629759633602521115150405337202372584340439034833221114403594442233918266196154388679017812693094048224675614710) (.leaf 521 6864794385913860325250622936435903531989770885575027517674172172221201517487807587909766930328929332927715851058641350228839455259633323986656891203940580319))) (.node (.node (.leaf 523 27030087578183496079519346090299653240693780933434041199266930211598172948499206671703487154346035874966031271295483032327009890092775786129834589183776096223) (.leaf 541 7198031242393724183618360480730994613839291367014779162932610646651620933790129713498660250417370701639977798796675371270252947542641429600414883857139610530217983)) (.node (.leaf 547 460628499636929298117471584689969500854276113430914683391169944199882114195967322163548485582281424243839679724797328371462479773438341114854306146976999613152624637) (.leaf 557 353456262032342462739811796020304034916498756017088906418554406409752562960620064496923072691351893205713678447241388928294292321470843569333852344215494636527320825339))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S3Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (48000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S3Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s3_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
