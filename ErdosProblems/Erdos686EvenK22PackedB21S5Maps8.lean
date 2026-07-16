import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s5_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (80000000 + (r.val : ZMod 499)) + 21))) = true →
      (1625981410900992108832931959835002592664162638699120347359548012918000058830043806650985201516673107616000557492879981424834160393888944618907088977919).testBit r.val = true := by decide

theorem even22_b21_s5_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (80000000 + (i : ZMod 499)) + 21))) = true) :
    (1625981410900992108832931959835002592664162638699120347359548012918000058830043806650985201516673107616000557492879981424834160393888944618907088977919).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_499_fin r
  change even22A499
    (-(33 * (46 * (80000000 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (80000000 + (r.val : ZMod 503)) + 21))) = true →
      (20970121072074489745656658116496444547103506950371253126067439629371158806318464184238319486356736121001630970421108551569931508166143917461955749593087).testBit r.val = true := by decide

theorem even22_b21_s5_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (80000000 + (i : ZMod 503)) + 21))) = true) :
    (20970121072074489745656658116496444547103506950371253126067439629371158806318464184238319486356736121001630970421108551569931508166143917461955749593087).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_503_fin r
  change even22A503
    (-(33 * (46 * (80000000 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (80000000 + (r.val : ZMod 509)) + 21))) = true →
      (830620467481017891515887536559302432246253624128661332001344212088195135842516292602126235127875043825481888058224900317383887091257820984579737412693751).testBit r.val = true := by decide

theorem even22_b21_s5_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (80000000 + (i : ZMod 509)) + 21))) = true) :
    (830620467481017891515887536559302432246253624128661332001344212088195135842516292602126235127875043825481888058224900317383887091257820984579737412693751).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_509_fin r
  change even22A509
    (-(33 * (46 * (80000000 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (80000000 + (r.val : ZMod 521)) + 21))) = true →
      (6536299741933637112364943433142818217987849151443597971881492845274536696655647347263851415567466160013457615235036314846238649565402800269598253370412105718).testBit r.val = true := by decide

theorem even22_b21_s5_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (80000000 + (i : ZMod 521)) + 21))) = true) :
    (6536299741933637112364943433142818217987849151443597971881492845274536696655647347263851415567466160013457615235036314846238649565402800269598253370412105718).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_521_fin r
  change even22A521
    (-(33 * (46 * (80000000 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (80000000 + (r.val : ZMod 523)) + 21))) = true →
      (12011716451259705636973216663381786026925667985244998743043125582916260198273135324453862153530781012649578354036799012752920785747464993239107419086367162295).testBit r.val = true := by decide

theorem even22_b21_s5_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (80000000 + (i : ZMod 523)) + 21))) = true) :
    (12011716451259705636973216663381786026925667985244998743043125582916260198273135324453862153530781012649578354036799012752920785747464993239107419086367162295).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_523_fin r
  change even22A523
    (-(33 * (46 * (80000000 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (80000000 + (r.val : ZMod 541)) + 21))) = true →
      (3479291565659174549098634917856946036919396530400464425039683507593939742857165471620433958922936470693784853187526968908205879928158930348796998965180693206252995).testBit r.val = true := by decide

theorem even22_b21_s5_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (80000000 + (i : ZMod 541)) + 21))) = true) :
    (3479291565659174549098634917856946036919396530400464425039683507593939742857165471620433958922936470693784853187526968908205879928158930348796998965180693206252995).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_541_fin r
  change even22A541
    (-(33 * (46 * (80000000 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (80000000 + (r.val : ZMod 547)) + 21))) = true →
      (460238881181349177614785197788405935269489302016803054647402920526553166266631674282422010977615841721598753285310551182064668390694848019493166696089150250510188521).testBit r.val = true := by decide

theorem even22_b21_s5_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (80000000 + (i : ZMod 547)) + 21))) = true) :
    (460238881181349177614785197788405935269489302016803054647402920526553166266631674282422010977615841721598753285310551182064668390694848019493166696089150250510188521).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_547_fin r
  change even22A547
    (-(33 * (46 * (80000000 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s5_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (80000000 + (r.val : ZMod 557)) + 21))) = true →
      (470679956086785906705149356403413318544484369870516587229369126785078373097993204590451724832517968469425996583489061303376408210013993845278696473432212879848829484415).testBit r.val = true := by decide

theorem even22_b21_s5_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (80000000 + (i : ZMod 557)) + 21))) = true) :
    (470679956086785906705149356403413318544484369870516587229369126785078373097993204590451724832517968469425996583489061303376408210013993845278696473432212879848829484415).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s5_map_557_fin r
  change even22A557
    (-(33 * (46 * (80000000 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S5Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1625981410900992108832931959835002592664162638699120347359548012918000058830043806650985201516673107616000557492879981424834160393888944618907088977919) (.leaf 503 20970121072074489745656658116496444547103506950371253126067439629371158806318464184238319486356736121001630970421108551569931508166143917461955749593087)) (.node (.leaf 509 830620467481017891515887536559302432246253624128661332001344212088195135842516292602126235127875043825481888058224900317383887091257820984579737412693751) (.leaf 521 6536299741933637112364943433142818217987849151443597971881492845274536696655647347263851415567466160013457615235036314846238649565402800269598253370412105718))) (.node (.node (.leaf 523 12011716451259705636973216663381786026925667985244998743043125582916260198273135324453862153530781012649578354036799012752920785747464993239107419086367162295) (.leaf 541 3479291565659174549098634917856946036919396530400464425039683507593939742857165471620433958922936470693784853187526968908205879928158930348796998965180693206252995)) (.node (.leaf 547 460238881181349177614785197788405935269489302016803054647402920526553166266631674282422010977615841721598753285310551182064668390694848019493166696089150250510188521) (.leaf 557 470679956086785906705149356403413318544484369870516587229369126785078373097993204590451724832517968469425996583489061303376408210013993845278696473432212879848829484415))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S5Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S5Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s5_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
