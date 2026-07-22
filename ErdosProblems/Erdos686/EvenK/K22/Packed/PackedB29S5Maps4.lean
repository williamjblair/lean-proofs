import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s5_map_307_fin : ∀ r : Fin 307,
    even22A307 (-(33 * (46 * (80000000 + (r.val : ZMod 307)) + 29))) = true →
      (260740348538468570382629366740746087283923107393790965798133162325987897867300753617142546359).testBit r.val = true := by decide

theorem even22_b29_s5_map_307 (i : ℕ)
    (h : even22A307 (-(33 * (46 * (80000000 + (i : ZMod 307)) + 29))) = true) :
    (260740348538468570382629366740746087283923107393790965798133162325987897867300753617142546359).testBit (i % 307) = true := by
  let r : Fin 307 := ⟨i % 307, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_307_fin r
  change even22A307
    (-(33 * (46 * (80000000 + ((i % 307 : ℕ) : ZMod 307)) + 29))) = true
  have hcast : (i : ZMod 307) = ((i % 307 : ℕ) : ZMod 307) :=
    (ZMod.natCast_mod i 307).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_311_fin : ∀ r : Fin 311,
    even22A311 (-(33 * (46 * (80000000 + (r.val : ZMod 311)) + 29))) = true →
      (4171762149668290631987728343293520542953580569769890379142589071151520275330751790072402280443).testBit r.val = true := by decide

theorem even22_b29_s5_map_311 (i : ℕ)
    (h : even22A311 (-(33 * (46 * (80000000 + (i : ZMod 311)) + 29))) = true) :
    (4171762149668290631987728343293520542953580569769890379142589071151520275330751790072402280443).testBit (i % 311) = true := by
  let r : Fin 311 := ⟨i % 311, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_311_fin r
  change even22A311
    (-(33 * (46 * (80000000 + ((i % 311 : ℕ) : ZMod 311)) + 29))) = true
  have hcast : (i : ZMod 311) = ((i % 311 : ℕ) : ZMod 311) :=
    (ZMod.natCast_mod i 311).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_313_fin : ∀ r : Fin 313,
    even22A313 (-(33 * (46 * (80000000 + (r.val : ZMod 313)) + 29))) = true →
      (8343699359066054082905759703612836618782543543374182284229051834831251657551550080573210885886).testBit r.val = true := by decide

theorem even22_b29_s5_map_313 (i : ℕ)
    (h : even22A313 (-(33 * (46 * (80000000 + (i : ZMod 313)) + 29))) = true) :
    (8343699359066054082905759703612836618782543543374182284229051834831251657551550080573210885886).testBit (i % 313) = true := by
  let r : Fin 313 := ⟨i % 313, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_313_fin r
  change even22A313
    (-(33 * (46 * (80000000 + ((i % 313 : ℕ) : ZMod 313)) + 29))) = true
  have hcast : (i : ZMod 313) = ((i % 313 : ℕ) : ZMod 313) :=
    (ZMod.natCast_mod i 313).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_317_fin : ∀ r : Fin 317,
    even22A317 (-(33 * (46 * (80000000 + (r.val : ZMod 317)) + 29))) = true →
      (241836911110427234536612215572011724966495778899380586710648341934543843316130897212876013942783).testBit r.val = true := by decide

theorem even22_b29_s5_map_317 (i : ℕ)
    (h : even22A317 (-(33 * (46 * (80000000 + (i : ZMod 317)) + 29))) = true) :
    (241836911110427234536612215572011724966495778899380586710648341934543843316130897212876013942783).testBit (i % 317) = true := by
  let r : Fin 317 := ⟨i % 317, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_317_fin r
  change even22A317
    (-(33 * (46 * (80000000 + ((i % 317 : ℕ) : ZMod 317)) + 29))) = true
  have hcast : (i : ZMod 317) = ((i % 317 : ℕ) : ZMod 317) :=
    (ZMod.natCast_mod i 317).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_331_fin : ∀ r : Fin 331,
    even22A331 (-(33 * (46 * (80000000 + (r.val : ZMod 331)) + 29))) = true →
      (4374364821486531539263386967531836760851810366510340668325742438308754322941623029574097558818390015).testBit r.val = true := by decide

theorem even22_b29_s5_map_331 (i : ℕ)
    (h : even22A331 (-(33 * (46 * (80000000 + (i : ZMod 331)) + 29))) = true) :
    (4374364821486531539263386967531836760851810366510340668325742438308754322941623029574097558818390015).testBit (i % 331) = true := by
  let r : Fin 331 := ⟨i % 331, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_331_fin r
  change even22A331
    (-(33 * (46 * (80000000 + ((i % 331 : ℕ) : ZMod 331)) + 29))) = true
  have hcast : (i : ZMod 331) = ((i % 331 : ℕ) : ZMod 331) :=
    (ZMod.natCast_mod i 331).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_337_fin : ∀ r : Fin 337,
    even22A337 (-(33 * (46 * (80000000 + (r.val : ZMod 337)) + 29))) = true →
      (173322464476251644791667456053102161807065316194084350942516739537089792564873374925331716057890553819).testBit r.val = true := by decide

theorem even22_b29_s5_map_337 (i : ℕ)
    (h : even22A337 (-(33 * (46 * (80000000 + (i : ZMod 337)) + 29))) = true) :
    (173322464476251644791667456053102161807065316194084350942516739537089792564873374925331716057890553819).testBit (i % 337) = true := by
  let r : Fin 337 := ⟨i % 337, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_337_fin r
  change even22A337
    (-(33 * (46 * (80000000 + ((i % 337 : ℕ) : ZMod 337)) + 29))) = true
  have hcast : (i : ZMod 337) = ((i % 337 : ℕ) : ZMod 337) :=
    (ZMod.natCast_mod i 337).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_347_fin : ∀ r : Fin 347,
    even22A347 (-(33 * (46 * (80000000 + (r.val : ZMod 347)) + 29))) = true →
      (250851410055920553120769920031012119666700019472953323508919814969434728168814593553006621621365090807807).testBit r.val = true := by decide

theorem even22_b29_s5_map_347 (i : ℕ)
    (h : even22A347 (-(33 * (46 * (80000000 + (i : ZMod 347)) + 29))) = true) :
    (250851410055920553120769920031012119666700019472953323508919814969434728168814593553006621621365090807807).testBit (i % 347) = true := by
  let r : Fin 347 := ⟨i % 347, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_347_fin r
  change even22A347
    (-(33 * (46 * (80000000 + ((i % 347 : ℕ) : ZMod 347)) + 29))) = true
  have hcast : (i : ZMod 347) = ((i % 347 : ℕ) : ZMod 347) :=
    (ZMod.natCast_mod i 347).symm
  rw [← hcast]
  exact h


theorem even22_b29_s5_map_349_fin : ∀ r : Fin 349,
    even22A349 (-(33 * (46 * (80000000 + (r.val : ZMod 349)) + 29))) = true →
      (860061707523186559421692575946429344467414040012223654549564505173614347629036575509287726811890164104687).testBit r.val = true := by decide

theorem even22_b29_s5_map_349 (i : ℕ)
    (h : even22A349 (-(33 * (46 * (80000000 + (i : ZMod 349)) + 29))) = true) :
    (860061707523186559421692575946429344467414040012223654549564505173614347629036575509287726811890164104687).testBit (i % 349) = true := by
  let r : Fin 349 := ⟨i % 349, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s5_map_349_fin r
  change even22A349
    (-(33 * (46 * (80000000 + ((i % 349 : ℕ) : ZMod 349)) + 29))) = true
  have hcast : (i : ZMod 349) = ((i % 349 : ℕ) : ZMod 349) :=
    (ZMod.natCast_mod i 349).symm
  rw [← hcast]
  exact h

def even22PackedB29S5Group4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 307 260740348538468570382629366740746087283923107393790965798133162325987897867300753617142546359) (.leaf 311 4171762149668290631987728343293520542953580569769890379142589071151520275330751790072402280443)) (.node (.leaf 313 8343699359066054082905759703612836618782543543374182284229051834831251657551550080573210885886) (.leaf 317 241836911110427234536612215572011724966495778899380586710648341934543843316130897212876013942783))) (.node (.node (.leaf 331 4374364821486531539263386967531836760851810366510340668325742438308754322941623029574097558818390015) (.leaf 337 173322464476251644791667456053102161807065316194084350942516739537089792564873374925331716057890553819)) (.node (.leaf 347 250851410055920553120769920031012119666700019472953323508919814969434728168814593553006621621365090807807) (.leaf 349 860061707523186559421692575946429344467414040012223654549564505173614347629036575509287726811890164104687))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S5Group4TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S5Group4Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_307 i
          have hA := even22_allowed_int even22A307 even22_allowed_307 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_311 i
          have hA := even22_allowed_int even22A311 even22_allowed_311 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_313 i
          have hA := even22_allowed_int even22A313 even22_allowed_313 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_317 i
          have hA := even22_allowed_int even22A317 even22_allowed_317 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_331 i
          have hA := even22_allowed_int even22A331 even22_allowed_331 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_337 i
          have hA := even22_allowed_int even22A337 even22_allowed_337 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_347 i
          have hA := even22_allowed_int even22A347 even22_allowed_347 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s5_map_349 i
          have hA := even22_allowed_int even22A349 even22_allowed_349 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
