import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s0_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (0 + (r.val : ZMod 449)) + 21))) = true →
      (1447998327794666913530203366351950147001309338035894306366113582239805489149561815426233204833052923174265267343339154375217167105785855).testBit r.val = true := by decide

theorem even22_b21_s0_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (0 + (i : ZMod 449)) + 21))) = true) :
    (1447998327794666913530203366351950147001309338035894306366113582239805489149561815426233204833052923174265267343339154375217167105785855).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_449_fin r
  change even22A449
    (-(33 * (46 * (0 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (0 + (r.val : ZMod 457)) + 21))) = true →
      (366321004998811118401830106185598175111507206638034815198022613256473824422832919489517455330140102794473804489825676538628148812585091007).testBit r.val = true := by decide

theorem even22_b21_s0_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (0 + (i : ZMod 457)) + 21))) = true) :
    (366321004998811118401830106185598175111507206638034815198022613256473824422832919489517455330140102794473804489825676538628148812585091007).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_457_fin r
  change even22A457
    (-(33 * (46 * (0 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (0 + (r.val : ZMod 461)) + 21))) = true →
      (5954254311786954799439730272674620812881051769709581730050215083506475289320080640661965340385119047816290329620707725292144676006981925885).testBit r.val = true := by decide

theorem even22_b21_s0_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (0 + (i : ZMod 461)) + 21))) = true) :
    (5954254311786954799439730272674620812881051769709581730050215083506475289320080640661965340385119047816290329620707725292144676006981925885).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_461_fin r
  change even22A461
    (-(33 * (46 * (0 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (0 + (r.val : ZMod 463)) + 21))) = true →
      (22305212575114739770067238685019321742849984634207583036777882980369192293269446698012928482351651285805148794829728549253963186464617906071).testBit r.val = true := by decide

theorem even22_b21_s0_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (0 + (i : ZMod 463)) + 21))) = true) :
    (22305212575114739770067238685019321742849984634207583036777882980369192293269446698012928482351651285805148794829728549253963186464617906071).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_463_fin r
  change even22A463
    (-(33 * (46 * (0 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (0 + (r.val : ZMod 467)) + 21))) = true →
      (130409039073454900606935398754902430324792835772234399947546999868552505713042065662377179954421008648551320060294929893400252987633521119103).testBit r.val = true := by decide

theorem even22_b21_s0_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (0 + (i : ZMod 467)) + 21))) = true) :
    (130409039073454900606935398754902430324792835772234399947546999868552505713042065662377179954421008648551320060294929893400252987633521119103).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_467_fin r
  change even22A467
    (-(33 * (46 * (0 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (0 + (r.val : ZMod 479)) + 21))) = true →
      (1164531534675234112544990652455086028107231834899551740517031111701151718357280172106020453579255294988084696358264426301741705201630247051558911).testBit r.val = true := by decide

theorem even22_b21_s0_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (0 + (i : ZMod 479)) + 21))) = true) :
    (1164531534675234112544990652455086028107231834899551740517031111701151718357280172106020453579255294988084696358264426301741705201630247051558911).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_479_fin r
  change even22A479
    (-(33 * (46 * (0 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (0 + (r.val : ZMod 487)) + 21))) = true →
      (398778416835383883408432002113163450316662711307951978144691040379113949198989935977384641899706291067105460701415571393818189827571992601353516989).testBit r.val = true := by decide

theorem even22_b21_s0_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (0 + (i : ZMod 487)) + 21))) = true) :
    (398778416835383883408432002113163450316662711307951978144691040379113949198989935977384641899706291067105460701415571393818189827571992601353516989).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_487_fin r
  change even22A487
    (-(33 * (46 * (0 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s0_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (0 + (r.val : ZMod 491)) + 21))) = true →
      (5817374598642447529035477454986194891495981369982484996745064993487961391570341932824710473410114157265892804163733336436955568044366787870788550631).testBit r.val = true := by decide

theorem even22_b21_s0_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (0 + (i : ZMod 491)) + 21))) = true) :
    (5817374598642447529035477454986194891495981369982484996745064993487961391570341932824710473410114157265892804163733336436955568044366787870788550631).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s0_map_491_fin r
  change even22A491
    (-(33 * (46 * (0 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S0Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1447998327794666913530203366351950147001309338035894306366113582239805489149561815426233204833052923174265267343339154375217167105785855) (.leaf 457 366321004998811118401830106185598175111507206638034815198022613256473824422832919489517455330140102794473804489825676538628148812585091007)) (.node (.leaf 461 5954254311786954799439730272674620812881051769709581730050215083506475289320080640661965340385119047816290329620707725292144676006981925885) (.leaf 463 22305212575114739770067238685019321742849984634207583036777882980369192293269446698012928482351651285805148794829728549253963186464617906071))) (.node (.node (.leaf 467 130409039073454900606935398754902430324792835772234399947546999868552505713042065662377179954421008648551320060294929893400252987633521119103) (.leaf 479 1164531534675234112544990652455086028107231834899551740517031111701151718357280172106020453579255294988084696358264426301741705201630247051558911)) (.node (.leaf 487 398778416835383883408432002113163450316662711307951978144691040379113949198989935977384641899706291067105460701415571393818189827571992601353516989) (.leaf 491 5817374598642447529035477454986194891495981369982484996745064993487961391570341932824710473410114157265892804163733336436955568044366787870788550631))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S0Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S0Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s0_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
