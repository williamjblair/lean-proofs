import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s4_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (64000000 + (r.val : ZMod 401)) + 29))) = true →
      (5164342109669335367249756994856230829594245947220187037663530125607138408636070069825267185802701119884171359301939478271).testBit r.val = true := by decide

theorem even22_b29_s4_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (64000000 + (i : ZMod 401)) + 29))) = true) :
    (5164342109669335367249756994856230829594245947220187037663530125607138408636070069825267185802701119884171359301939478271).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_401_fin r
  change even22A401
    (-(33 * (46 * (64000000 + ((i % 401 : ℕ) : ZMod 401)) + 29))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (64000000 + (r.val : ZMod 409)) + 29))) = true →
      (1322111937580421833395964356839310817678893333240567232186973596768308156866698550532192585670349350118545842330893530890111).testBit r.val = true := by decide

theorem even22_b29_s4_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (64000000 + (i : ZMod 409)) + 29))) = true) :
    (1322111937580421833395964356839310817678893333240567232186973596768308156866698550532192585670349350118545842330893530890111).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_409_fin r
  change even22A409
    (-(33 * (46 * (64000000 + ((i % 409 : ℕ) : ZMod 409)) + 29))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (64000000 + (r.val : ZMod 419)) + 29))) = true →
      (1343265244247394617822256744469606821465107785659365073675232172027175954619111351240649776957146525705860255721508286358355711).testBit r.val = true := by decide

theorem even22_b29_s4_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (64000000 + (i : ZMod 419)) + 29))) = true) :
    (1343265244247394617822256744469606821465107785659365073675232172027175954619111351240649776957146525705860255721508286358355711).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_419_fin r
  change even22A419
    (-(33 * (46 * (64000000 + ((i % 419 : ℕ) : ZMod 419)) + 29))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (64000000 + (r.val : ZMod 421)) + 29))) = true →
      (3383945504227432067091584811001112007027513244328513653487315593052012862051931712144435042083620215860031707212818451301117919).testBit r.val = true := by decide

theorem even22_b29_s4_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (64000000 + (i : ZMod 421)) + 29))) = true) :
    (3383945504227432067091584811001112007027513244328513653487315593052012862051931712144435042083620215860031707212818451301117919).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_421_fin r
  change even22A421
    (-(33 * (46 * (64000000 + ((i % 421 : ℕ) : ZMod 421)) + 29))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (64000000 + (r.val : ZMod 431)) + 29))) = true →
      (3855743710714350651312910307813313600098001427768565922727682254772637702043291519018705942542294276864382012122455116491056478207).testBit r.val = true := by decide

theorem even22_b29_s4_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (64000000 + (i : ZMod 431)) + 29))) = true) :
    (3855743710714350651312910307813313600098001427768565922727682254772637702043291519018705942542294276864382012122455116491056478207).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_431_fin r
  change even22A431
    (-(33 * (46 * (64000000 + ((i % 431 : ℕ) : ZMod 431)) + 29))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (64000000 + (r.val : ZMod 433)) + 29))) = true →
      (22181187661582203594084936893476179041926341952070917644438760984676074537024299352401808497613107300052563010009078843209517367039).testBit r.val = true := by decide

theorem even22_b29_s4_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (64000000 + (i : ZMod 433)) + 29))) = true) :
    (22181187661582203594084936893476179041926341952070917644438760984676074537024299352401808497613107300052563010009078843209517367039).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_433_fin r
  change even22A433
    (-(33 * (46 * (64000000 + ((i % 433 : ℕ) : ZMod 433)) + 29))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (64000000 + (r.val : ZMod 439)) + 29))) = true →
      (1344555178734946582085292427652722340747275318356463969791392491864681706122276799170998623226252323244805840844531430208253009592255).testBit r.val = true := by decide

theorem even22_b29_s4_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (64000000 + (i : ZMod 439)) + 29))) = true) :
    (1344555178734946582085292427652722340747275318356463969791392491864681706122276799170998623226252323244805840844531430208253009592255).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_439_fin r
  change even22A439
    (-(33 * (46 * (64000000 + ((i % 439 : ℕ) : ZMod 439)) + 29))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b29_s4_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (64000000 + (r.val : ZMod 443)) + 29))) = true →
      (22669340395866264250652722590139624077396037948603369862339189554226399080732887585425069459496347470575611995882033176915755287314415).testBit r.val = true := by decide

theorem even22_b29_s4_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (64000000 + (i : ZMod 443)) + 29))) = true) :
    (22669340395866264250652722590139624077396037948603369862339189554226399080732887585425069459496347470575611995882033176915755287314415).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s4_map_443_fin r
  change even22A443
    (-(33 * (46 * (64000000 + ((i % 443 : ℕ) : ZMod 443)) + 29))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB29S4Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5164342109669335367249756994856230829594245947220187037663530125607138408636070069825267185802701119884171359301939478271) (.leaf 409 1322111937580421833395964356839310817678893333240567232186973596768308156866698550532192585670349350118545842330893530890111)) (.node (.leaf 419 1343265244247394617822256744469606821465107785659365073675232172027175954619111351240649776957146525705860255721508286358355711) (.leaf 421 3383945504227432067091584811001112007027513244328513653487315593052012862051931712144435042083620215860031707212818451301117919))) (.node (.node (.leaf 431 3855743710714350651312910307813313600098001427768565922727682254772637702043291519018705942542294276864382012122455116491056478207) (.leaf 433 22181187661582203594084936893476179041926341952070917644438760984676074537024299352401808497613107300052563010009078843209517367039)) (.node (.leaf 439 1344555178734946582085292427652722340747275318356463969791392491864681706122276799170998623226252323244805840844531430208253009592255) (.leaf 443 22669340395866264250652722590139624077396037948603369862339189554226399080732887585425069459496347470575611995882033176915755287314415))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S4Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S4Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s4_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
