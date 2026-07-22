import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s2_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (32000000 + (r.val : ZMod 449)) + 17))) = true →
      (1406826912277201071652684245159409915581923206189055937360922872605140174033427107106321790367485677447140227436112431092097146342864895).testBit r.val = true := by decide

theorem even22_b17_s2_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (32000000 + (i : ZMod 449)) + 17))) = true) :
    (1406826912277201071652684245159409915581923206189055937360922872605140174033427107106321790367485677447140227436112431092097146342864895).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_449_fin r
  change even22A449
    (-(33 * (46 * (32000000 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (32000000 + (r.val : ZMod 457)) + 17))) = true →
      (353243575471615679389048061740818700150144472108993922678376536232112543060378013436942486887594239769955203647816382913509607178971905535).testBit r.val = true := by decide

theorem even22_b17_s2_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (32000000 + (i : ZMod 457)) + 17))) = true) :
    (353243575471615679389048061740818700150144472108993922678376536232112543060378013436942486887594239769955203647816382913509607178971905535).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_457_fin r
  change even22A457
    (-(33 * (46 * (32000000 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (32000000 + (r.val : ZMod 461)) + 17))) = true →
      (5207072619467349896551742980170441632837253933126000304025669527650865341256697540291560827103273233565794178182560941850955067895167440895).testBit r.val = true := by decide

theorem even22_b17_s2_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (32000000 + (i : ZMod 461)) + 17))) = true) :
    (5207072619467349896551742980170441632837253933126000304025669527650865341256697540291560827103273233565794178182560941850955067895167440895).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_461_fin r
  change even22A461
    (-(33 * (46 * (32000000 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (32000000 + (r.val : ZMod 463)) + 17))) = true →
      (23817042594725617378787579782944474743448788028285515604370054940304355534202049745617604070069944399469685199098939880395985805112413707519).testBit r.val = true := by decide

theorem even22_b17_s2_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (32000000 + (i : ZMod 463)) + 17))) = true) :
    (23817042594725617378787579782944474743448788028285515604370054940304355534202049745617604070069944399469685199098939880395985805112413707519).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_463_fin r
  change even22A463
    (-(33 * (46 * (32000000 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (32000000 + (r.val : ZMod 467)) + 17))) = true →
      (377897951827049474894082316937894741130637015504723142473931206396366580921611564809908183922118462862515619761662977936196580725621226471389).testBit r.val = true := by decide

theorem even22_b17_s2_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (32000000 + (i : ZMod 467)) + 17))) = true) :
    (377897951827049474894082316937894741130637015504723142473931206396366580921611564809908183922118462862515619761662977936196580725621226471389).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_467_fin r
  change even22A467
    (-(33 * (46 * (32000000 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (32000000 + (r.val : ZMod 479)) + 17))) = true →
      (559581620709740785358012284622265716860523798726822920419727920213561561830852219227603383489988432216543246540853439480360041142319109587855191).testBit r.val = true := by decide

theorem even22_b17_s2_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (32000000 + (i : ZMod 479)) + 17))) = true) :
    (559581620709740785358012284622265716860523798726822920419727920213561561830852219227603383489988432216543246540853439480360041142319109587855191).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_479_fin r
  change even22A479
    (-(33 * (46 * (32000000 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (32000000 + (r.val : ZMod 487)) + 17))) = true →
      (293442741192991217886546216825941949682904660665819479536142046682923057326584226634975630268679474402354682763210142132525752229990515351126768895).testBit r.val = true := by decide

theorem even22_b17_s2_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (32000000 + (i : ZMod 487)) + 17))) = true) :
    (293442741192991217886546216825941949682904660665819479536142046682923057326584226634975630268679474402354682763210142132525752229990515351126768895).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_487_fin r
  change even22A487
    (-(33 * (46 * (32000000 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s2_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (32000000 + (r.val : ZMod 491)) + 17))) = true →
      (6384754673680789740776689536277500572364714349502336792120421852979471521503574096116918060955878906109545321427378938734385895029965865499344486347).testBit r.val = true := by decide

theorem even22_b17_s2_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (32000000 + (i : ZMod 491)) + 17))) = true) :
    (6384754673680789740776689536277500572364714349502336792120421852979471521503574096116918060955878906109545321427378938734385895029965865499344486347).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s2_map_491_fin r
  change even22A491
    (-(33 * (46 * (32000000 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S2Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1406826912277201071652684245159409915581923206189055937360922872605140174033427107106321790367485677447140227436112431092097146342864895) (.leaf 457 353243575471615679389048061740818700150144472108993922678376536232112543060378013436942486887594239769955203647816382913509607178971905535)) (.node (.leaf 461 5207072619467349896551742980170441632837253933126000304025669527650865341256697540291560827103273233565794178182560941850955067895167440895) (.leaf 463 23817042594725617378787579782944474743448788028285515604370054940304355534202049745617604070069944399469685199098939880395985805112413707519))) (.node (.node (.leaf 467 377897951827049474894082316937894741130637015504723142473931206396366580921611564809908183922118462862515619761662977936196580725621226471389) (.leaf 479 559581620709740785358012284622265716860523798726822920419727920213561561830852219227603383489988432216543246540853439480360041142319109587855191)) (.node (.leaf 487 293442741192991217886546216825941949682904660665819479536142046682923057326584226634975630268679474402354682763210142132525752229990515351126768895) (.leaf 491 6384754673680789740776689536277500572364714349502336792120421852979471521503574096116918060955878906109545321427378938734385895029965865499344486347))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S2Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S2Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s2_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
