import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s0_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (0 + (r.val : ZMod 499)) + 21))) = true →
      (1636295328366860236638163386994076833038300350858758178254385338570109817287138781656645463784905592824824278629882810886488376282801827428944467322687).testBit r.val = true := by decide

theorem even22_b21_s0_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (0 + (i : ZMod 499)) + 21))) = true) :
    (1636295328366860236638163386994076833038300350858758178254385338570109817287138781656645463784905592824824278629882810886488376282801827428944467322687).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_499_fin r
  change even22A499
    (-(33 * (46 * (0 + ((i % 499 : ℕ) : ZMod 499)) + 21))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (0 + (r.val : ZMod 503)) + 21))) = true →
      (26024094642488742958920750679301562566621940230705333181558336953238314394425805638922377227126730860686902810109775450573967834427493100548026418585551).testBit r.val = true := by decide

theorem even22_b21_s0_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (0 + (i : ZMod 503)) + 21))) = true) :
    (26024094642488742958920750679301562566621940230705333181558336953238314394425805638922377227126730860686902810109775450573967834427493100548026418585551).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_503_fin r
  change even22A503
    (-(33 * (46 * (0 + ((i % 503 : ℕ) : ZMod 503)) + 21))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (0 + (r.val : ZMod 509)) + 21))) = true →
      (818115880068302316107777297795096720835235143206005821840112580175311789551281444396548785274606068133555448126770950369510817927433806739319286904094715).testBit r.val = true := by decide

theorem even22_b21_s0_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (0 + (i : ZMod 509)) + 21))) = true) :
    (818115880068302316107777297795096720835235143206005821840112580175311789551281444396548785274606068133555448126770950369510817927433806739319286904094715).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_509_fin r
  change even22A509
    (-(33 * (46 * (0 + ((i % 509 : ℕ) : ZMod 509)) + 21))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (0 + (r.val : ZMod 521)) + 21))) = true →
      (6831061070381869205855030304243859453282435546838409184527166929022786580126956639790845730571517060955501771223032595560121402340915139492443672721569349631).testBit r.val = true := by decide

theorem even22_b21_s0_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (0 + (i : ZMod 521)) + 21))) = true) :
    (6831061070381869205855030304243859453282435546838409184527166929022786580126956639790845730571517060955501771223032595560121402340915139492443672721569349631).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_521_fin r
  change even22A521
    (-(33 * (46 * (0 + ((i % 521 : ℕ) : ZMod 521)) + 21))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (0 + (r.val : ZMod 523)) + 21))) = true →
      (13729176326062836284176609274166999698626012426794359270854938970578099484004924541325617277425343962402796544895547255993403221011668140924780176487198097332).testBit r.val = true := by decide

theorem even22_b21_s0_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (0 + (i : ZMod 523)) + 21))) = true) :
    (13729176326062836284176609274166999698626012426794359270854938970578099484004924541325617277425343962402796544895547255993403221011668140924780176487198097332).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_523_fin r
  change even22A523
    (-(33 * (46 * (0 + ((i % 523 : ℕ) : ZMod 523)) + 21))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (0 + (r.val : ZMod 541)) + 21))) = true →
      (6962723766783355199357839708140464870307718670862106879471787223061804035870886105114873002975676656980677967795045101561485994726772741888408030131916760781012991).testBit r.val = true := by decide

theorem even22_b21_s0_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (0 + (i : ZMod 541)) + 21))) = true) :
    (6962723766783355199357839708140464870307718670862106879471787223061804035870886105114873002975676656980677967795045101561485994726772741888408030131916760781012991).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_541_fin r
  change even22A541
    (-(33 * (46 * (0 + ((i % 541 : ℕ) : ZMod 541)) + 21))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (0 + (r.val : ZMod 547)) + 21))) = true →
      (460688770843662156026393960218342334187461773139737338222685550275541499599677999389142506251146049482526913575745810730045997614031876953499382513881809564085516283).testBit r.val = true := by decide

theorem even22_b21_s0_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (0 + (i : ZMod 547)) + 21))) = true) :
    (460688770843662156026393960218342334187461773139737338222685550275541499599677999389142506251146049482526913575745810730045997614031876953499382513881809564085516283).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_547_fin r
  change even22A547
    (-(33 * (46 * (0 + ((i % 547 : ℕ) : ZMod 547)) + 21))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (0 + (r.val : ZMod 557)) + 21))) = true →
      (342521961119585070881957714597290561402533732643398769102684102506192854718697528073665711413183324339796409766188828839358652886826217501023963566722249319685453511673).testBit r.val = true := by decide

theorem even22_b21_s0_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (0 + (i : ZMod 557)) + 21))) = true) :
    (342521961119585070881957714597290561402533732643398769102684102506192854718697528073665711413183324339796409766188828839358652886826217501023963566722249319685453511673).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_557_fin r
  change even22A557
    (-(33 * (46 * (0 + ((i % 557 : ℕ) : ZMod 557)) + 21))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB21S0Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1636295328366860236638163386994076833038300350858758178254385338570109817287138781656645463784905592824824278629882810886488376282801827428944467322687) (.leaf 503 26024094642488742958920750679301562566621940230705333181558336953238314394425805638922377227126730860686902810109775450573967834427493100548026418585551)) (.node (.leaf 509 818115880068302316107777297795096720835235143206005821840112580175311789551281444396548785274606068133555448126770950369510817927433806739319286904094715) (.leaf 521 6831061070381869205855030304243859453282435546838409184527166929022786580126956639790845730571517060955501771223032595560121402340915139492443672721569349631))) (.node (.node (.leaf 523 13729176326062836284176609274166999698626012426794359270854938970578099484004924541325617277425343962402796544895547255993403221011668140924780176487198097332) (.leaf 541 6962723766783355199357839708140464870307718670862106879471787223061804035870886105114873002975676656980677967795045101561485994726772741888408030131916760781012991)) (.node (.leaf 547 460688770843662156026393960218342334187461773139737338222685550275541499599677999389142506251146049482526913575745810730045997614031876953499382513881809564085516283) (.leaf 557 342521961119585070881957714597290561402533732643398769102684102506192854718697528073665711413183324339796409766188828839358652886826217501023963566722249319685453511673))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S0Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S0Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
