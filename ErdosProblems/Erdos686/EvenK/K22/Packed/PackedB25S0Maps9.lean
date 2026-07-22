import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s0_map_563_fin : ∀ r : Fin 563,
    even22A563 (-(33 * (46 * (0 + (r.val : ZMod 563)) + 25))) = true →
      (30073763036770078858145649842226784448392949753528244538477732400073843356412613417884900687920301649706161347276571317845566043009599242419962832740761027426244099571145).testBit r.val = true := by decide

theorem even22_b25_s0_map_563 (i : ℕ)
    (h : even22A563 (-(33 * (46 * (0 + (i : ZMod 563)) + 25))) = true) :
    (30073763036770078858145649842226784448392949753528244538477732400073843356412613417884900687920301649706161347276571317845566043009599242419962832740761027426244099571145).testBit (i % 563) = true := by
  let r : Fin 563 := ⟨i % 563, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_563_fin r
  change even22A563
    (-(33 * (46 * (0 + ((i % 563 : ℕ) : ZMod 563)) + 25))) = true
  have hcast : (i : ZMod 563) = ((i % 563 : ℕ) : ZMod 563) :=
    (ZMod.natCast_mod i 563).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_569_fin : ∀ r : Fin 569,
    even22A569 (-(33 * (46 * (0 + (r.val : ZMod 569)) + 25))) = true →
      (1932251681830542173592901815606420469049054506169087487627325625798719230123060742369704200631485857425209710565549577930781036503366901337836219377679859960614568476011391).testBit r.val = true := by decide

theorem even22_b25_s0_map_569 (i : ℕ)
    (h : even22A569 (-(33 * (46 * (0 + (i : ZMod 569)) + 25))) = true) :
    (1932251681830542173592901815606420469049054506169087487627325625798719230123060742369704200631485857425209710565549577930781036503366901337836219377679859960614568476011391).testBit (i % 569) = true := by
  let r : Fin 569 := ⟨i % 569, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_569_fin r
  change even22A569
    (-(33 * (46 * (0 + ((i % 569 : ℕ) : ZMod 569)) + 25))) = true
  have hcast : (i : ZMod 569) = ((i % 569 : ℕ) : ZMod 569) :=
    (ZMod.natCast_mod i 569).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_571_fin : ∀ r : Fin 571,
    even22A571 (-(33 * (46 * (0 + (r.val : ZMod 571)) + 25))) = true →
      (7666789691276042209992086683344995375497277011437912270652641792005018834914194541119464301610707676294718544384346735404941296954439801838025715630834867115165982228115455).testBit r.val = true := by decide

theorem even22_b25_s0_map_571 (i : ℕ)
    (h : even22A571 (-(33 * (46 * (0 + (i : ZMod 571)) + 25))) = true) :
    (7666789691276042209992086683344995375497277011437912270652641792005018834914194541119464301610707676294718544384346735404941296954439801838025715630834867115165982228115455).testBit (i % 571) = true := by
  let r : Fin 571 := ⟨i % 571, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_571_fin r
  change even22A571
    (-(33 * (46 * (0 + ((i % 571 : ℕ) : ZMod 571)) + 25))) = true
  have hcast : (i : ZMod 571) = ((i % 571 : ℕ) : ZMod 571) :=
    (ZMod.natCast_mod i 571).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_577_fin : ∀ r : Fin 577,
    even22A577 (-(33 * (46 * (0 + (r.val : ZMod 577)) + 25))) = true →
      (492709192555283523149142871586309199901477439596054500978774379818910548131530037594321370833693653338678193638570447491957082864226963691849083595062893333068495913903583103).testBit r.val = true := by decide

theorem even22_b25_s0_map_577 (i : ℕ)
    (h : even22A577 (-(33 * (46 * (0 + (i : ZMod 577)) + 25))) = true) :
    (492709192555283523149142871586309199901477439596054500978774379818910548131530037594321370833693653338678193638570447491957082864226963691849083595062893333068495913903583103).testBit (i % 577) = true := by
  let r : Fin 577 := ⟨i % 577, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_577_fin r
  change even22A577
    (-(33 * (46 * (0 + ((i % 577 : ℕ) : ZMod 577)) + 25))) = true
  have hcast : (i : ZMod 577) = ((i % 577 : ℕ) : ZMod 577) :=
    (ZMod.natCast_mod i 577).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_587_fin : ∀ r : Fin 587,
    even22A587 (-(33 * (46 * (0 + (r.val : ZMod 587)) + 25))) = true →
      (504300830912574529702009220247069065888605297710134790467247778780667655431734568897432839382024734498138052590327485235925323446805966256622349160510211847067652346243299509727).testBit r.val = true := by decide

theorem even22_b25_s0_map_587 (i : ℕ)
    (h : even22A587 (-(33 * (46 * (0 + (i : ZMod 587)) + 25))) = true) :
    (504300830912574529702009220247069065888605297710134790467247778780667655431734568897432839382024734498138052590327485235925323446805966256622349160510211847067652346243299509727).testBit (i % 587) = true := by
  let r : Fin 587 := ⟨i % 587, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_587_fin r
  change even22A587
    (-(33 * (46 * (0 + ((i % 587 : ℕ) : ZMod 587)) + 25))) = true
  have hcast : (i : ZMod 587) = ((i % 587 : ℕ) : ZMod 587) :=
    (ZMod.natCast_mod i 587).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_593_fin : ∀ r : Fin 593,
    even22A593 (-(33 * (46 * (0 + (r.val : ZMod 593)) + 25))) = true →
      (32418067192769802945333469768648365588699161400831491025928324222083664214312081365982067447045708947688862014098860470931618338703104422619986991489511764150311844169590476885871).testBit r.val = true := by decide

theorem even22_b25_s0_map_593 (i : ℕ)
    (h : even22A593 (-(33 * (46 * (0 + (i : ZMod 593)) + 25))) = true) :
    (32418067192769802945333469768648365588699161400831491025928324222083664214312081365982067447045708947688862014098860470931618338703104422619986991489511764150311844169590476885871).testBit (i % 593) = true := by
  let r : Fin 593 := ⟨i % 593, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_593_fin r
  change even22A593
    (-(33 * (46 * (0 + ((i % 593 : ℕ) : ZMod 593)) + 25))) = true
  have hcast : (i : ZMod 593) = ((i % 593 : ℕ) : ZMod 593) :=
    (ZMod.natCast_mod i 593).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_599_fin : ∀ r : Fin 599,
    even22A599 (-(33 * (46 * (0 + (r.val : ZMod 599)) + 25))) = true →
      (1944301833824746654677674170371188999899119397922233180289533570663404386180594079978229197705531140105962842276064371987226649129620062313087677992117508125200544592050878282726399).testBit r.val = true := by decide

theorem even22_b25_s0_map_599 (i : ℕ)
    (h : even22A599 (-(33 * (46 * (0 + (i : ZMod 599)) + 25))) = true) :
    (1944301833824746654677674170371188999899119397922233180289533570663404386180594079978229197705531140105962842276064371987226649129620062313087677992117508125200544592050878282726399).testBit (i % 599) = true := by
  let r : Fin 599 := ⟨i % 599, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_599_fin r
  change even22A599
    (-(33 * (46 * (0 + ((i % 599 : ℕ) : ZMod 599)) + 25))) = true
  have hcast : (i : ZMod 599) = ((i % 599 : ℕ) : ZMod 599) :=
    (ZMod.natCast_mod i 599).symm
  rw [← hcast]
  exact h


theorem even22_b25_s0_map_601_fin : ∀ r : Fin 601,
    even22A601 (-(33 * (46 * (0 + (r.val : ZMod 601)) + 25))) = true →
      (8298903515236967543250501942730114584767715744633209850848764004953990083747925880329706588193310329260202631122284166135777092495528053832961516131766154402476636932137534942604767).testBit r.val = true := by decide

theorem even22_b25_s0_map_601 (i : ℕ)
    (h : even22A601 (-(33 * (46 * (0 + (i : ZMod 601)) + 25))) = true) :
    (8298903515236967543250501942730114584767715744633209850848764004953990083747925880329706588193310329260202631122284166135777092495528053832961516131766154402476636932137534942604767).testBit (i % 601) = true := by
  let r : Fin 601 := ⟨i % 601, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s0_map_601_fin r
  change even22A601
    (-(33 * (46 * (0 + ((i % 601 : ℕ) : ZMod 601)) + 25))) = true
  have hcast : (i : ZMod 601) = ((i % 601 : ℕ) : ZMod 601) :=
    (ZMod.natCast_mod i 601).symm
  rw [← hcast]
  exact h

def even22PackedB25S0Group9Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 563 30073763036770078858145649842226784448392949753528244538477732400073843356412613417884900687920301649706161347276571317845566043009599242419962832740761027426244099571145) (.leaf 569 1932251681830542173592901815606420469049054506169087487627325625798719230123060742369704200631485857425209710565549577930781036503366901337836219377679859960614568476011391)) (.node (.leaf 571 7666789691276042209992086683344995375497277011437912270652641792005018834914194541119464301610707676294718544384346735404941296954439801838025715630834867115165982228115455) (.leaf 577 492709192555283523149142871586309199901477439596054500978774379818910548131530037594321370833693653338678193638570447491957082864226963691849083595062893333068495913903583103))) (.node (.node (.leaf 587 504300830912574529702009220247069065888605297710134790467247778780667655431734568897432839382024734498138052590327485235925323446805966256622349160510211847067652346243299509727) (.leaf 593 32418067192769802945333469768648365588699161400831491025928324222083664214312081365982067447045708947688862014098860470931618338703104422619986991489511764150311844169590476885871)) (.node (.leaf 599 1944301833824746654677674170371188999899119397922233180289533570663404386180594079978229197705531140105962842276064371987226649129620062313087677992117508125200544592050878282726399) (.leaf 601 8298903515236967543250501942730114584767715744633209850848764004953990083747925880329706588193310329260202631122284166135777092495528053832961516131766154402476636932137534942604767))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S0Group9TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S0Group9Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_563 i
          have hA := even22_allowed_int even22A563 even22_allowed_563 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_569 i
          have hA := even22_allowed_int even22A569 even22_allowed_569 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_571 i
          have hA := even22_allowed_int even22A571 even22_allowed_571 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_577 i
          have hA := even22_allowed_int even22A577 even22_allowed_577 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_587 i
          have hA := even22_allowed_int even22A587 even22_allowed_587 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_593 i
          have hA := even22_allowed_int even22A593 even22_allowed_593 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_599 i
          have hA := even22_allowed_int even22A599 even22_allowed_599 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s0_map_601 i
          have hA := even22_allowed_int even22A601 even22_allowed_601 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
