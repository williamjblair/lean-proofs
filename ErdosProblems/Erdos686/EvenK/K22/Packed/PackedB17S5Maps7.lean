import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s5_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (80000000 + (r.val : ZMod 449)) + 17))) = true →
      (1452257668415968016122022893685157065275817738009418779484840352919030207372449796100471581801037806797394104731703694111416572778100663).testBit r.val = true := by decide

theorem even22_b17_s5_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (80000000 + (i : ZMod 449)) + 17))) = true) :
    (1452257668415968016122022893685157065275817738009418779484840352919030207372449796100471581801037806797394104731703694111416572778100663).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_449_fin r
  change even22A449
    (-(33 * (46 * (80000000 + ((i % 449 : ℕ) : ZMod 449)) + 17))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (80000000 + (r.val : ZMod 457)) + 17))) = true →
      (371777650474317002363789809422842062434217053544789844884991708935236472320858060664666545300740267893820623151621870191760868082521603067).testBit r.val = true := by decide

theorem even22_b17_s5_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (80000000 + (i : ZMod 457)) + 17))) = true) :
    (371777650474317002363789809422842062434217053544789844884991708935236472320858060664666545300740267893820623151621870191760868082521603067).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_457_fin r
  change even22A457
    (-(33 * (46 * (80000000 + ((i % 457 : ℕ) : ZMod 457)) + 17))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (80000000 + (r.val : ZMod 461)) + 17))) = true →
      (4372661752190836163828731665750010533053450977577414089216983258393953063964379892349410911965264054957125774219350962059640388582073417695).testBit r.val = true := by decide

theorem even22_b17_s5_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (80000000 + (i : ZMod 461)) + 17))) = true) :
    (4372661752190836163828731665750010533053450977577414089216983258393953063964379892349410911965264054957125774219350962059640388582073417695).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_461_fin r
  change even22A461
    (-(33 * (46 * (80000000 + ((i % 461 : ℕ) : ZMod 461)) + 17))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (80000000 + (r.val : ZMod 463)) + 17))) = true →
      (17105417557511458042197849412342612995297036824123469118758932711515739431087537434497825696325353051108509963875452232720324736401914461951).testBit r.val = true := by decide

theorem even22_b17_s5_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (80000000 + (i : ZMod 463)) + 17))) = true) :
    (17105417557511458042197849412342612995297036824123469118758932711515739431087537434497825696325353051108509963875452232720324736401914461951).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_463_fin r
  change even22A463
    (-(33 * (46 * (80000000 + ((i % 463 : ℕ) : ZMod 463)) + 17))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (80000000 + (r.val : ZMod 467)) + 17))) = true →
      (278267263814385174361893159254671886684062511657636528140295522749660015201971949726706193404016509745661080436421114839463972343836611376111).testBit r.val = true := by decide

theorem even22_b17_s5_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (80000000 + (i : ZMod 467)) + 17))) = true) :
    (278267263814385174361893159254671886684062511657636528140295522749660015201971949726706193404016509745661080436421114839463972343836611376111).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_467_fin r
  change even22A467
    (-(33 * (46 * (80000000 + ((i % 467 : ℕ) : ZMod 467)) + 17))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (80000000 + (r.val : ZMod 479)) + 17))) = true →
      (1554753290061965048258454648197328955715917362187882982971341972096635239629102553144474881435122367268226340174332275852875693131145880758385631).testBit r.val = true := by decide

theorem even22_b17_s5_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (80000000 + (i : ZMod 479)) + 17))) = true) :
    (1554753290061965048258454648197328955715917362187882982971341972096635239629102553144474881435122367268226340174332275852875693131145880758385631).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_479_fin r
  change even22A479
    (-(33 * (46 * (80000000 + ((i % 479 : ℕ) : ZMod 479)) + 17))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (80000000 + (r.val : ZMod 487)) + 17))) = true →
      (399169171293639901683170596430619610308162639101008797762794663163179038844955885923184255093589482949774956552076863803316747932899045394012436411).testBit r.val = true := by decide

theorem even22_b17_s5_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (80000000 + (i : ZMod 487)) + 17))) = true) :
    (399169171293639901683170596430619610308162639101008797762794663163179038844955885923184255093589482949774956552076863803316747932899045394012436411).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_487_fin r
  change even22A487
    (-(33 * (46 * (80000000 + ((i % 487 : ℕ) : ZMod 487)) + 17))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b17_s5_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (80000000 + (r.val : ZMod 491)) + 17))) = true →
      (4670131241233734073189398630387488490074727690098585579934900913528405957532314786008420244600286494804992712298288538070544382792229616673455341502).testBit r.val = true := by decide

theorem even22_b17_s5_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (80000000 + (i : ZMod 491)) + 17))) = true) :
    (4670131241233734073189398630387488490074727690098585579934900913528405957532314786008420244600286494804992712298288538070544382792229616673455341502).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s5_map_491_fin r
  change even22A491
    (-(33 * (46 * (80000000 + ((i % 491 : ℕ) : ZMod 491)) + 17))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB17S5Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1452257668415968016122022893685157065275817738009418779484840352919030207372449796100471581801037806797394104731703694111416572778100663) (.leaf 457 371777650474317002363789809422842062434217053544789844884991708935236472320858060664666545300740267893820623151621870191760868082521603067)) (.node (.leaf 461 4372661752190836163828731665750010533053450977577414089216983258393953063964379892349410911965264054957125774219350962059640388582073417695) (.leaf 463 17105417557511458042197849412342612995297036824123469118758932711515739431087537434497825696325353051108509963875452232720324736401914461951))) (.node (.node (.leaf 467 278267263814385174361893159254671886684062511657636528140295522749660015201971949726706193404016509745661080436421114839463972343836611376111) (.leaf 479 1554753290061965048258454648197328955715917362187882982971341972096635239629102553144474881435122367268226340174332275852875693131145880758385631)) (.node (.leaf 487 399169171293639901683170596430619610308162639101008797762794663163179038844955885923184255093589482949774956552076863803316747932899045394012436411) (.leaf 491 4670131241233734073189398630387488490074727690098585579934900913528405957532314786008420244600286494804992712298288538070544382792229616673455341502))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S5Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S5Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s5_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
