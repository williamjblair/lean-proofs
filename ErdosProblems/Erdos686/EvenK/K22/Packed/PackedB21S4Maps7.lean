import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s4_map_449_fin : ∀ r : Fin 449,
    even22A449 (-(33 * (46 * (64000000 + (r.val : ZMod 449)) + 21))) = true →
      (1452257645992939249714005721511409964532055414628489609883584168474624851865866668718498687364566304105704408805114547490652791158865911).testBit r.val = true := by decide

theorem even22_b21_s4_map_449 (i : ℕ)
    (h : even22A449 (-(33 * (46 * (64000000 + (i : ZMod 449)) + 21))) = true) :
    (1452257645992939249714005721511409964532055414628489609883584168474624851865866668718498687364566304105704408805114547490652791158865911).testBit (i % 449) = true := by
  let r : Fin 449 := ⟨i % 449, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_449_fin r
  change even22A449
    (-(33 * (46 * (64000000 + ((i % 449 : ℕ) : ZMod 449)) + 21))) = true
  have hcast : (i : ZMod 449) = ((i % 449 : ℕ) : ZMod 449) :=
    (ZMod.natCast_mod i 449).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_457_fin : ∀ r : Fin 457,
    even22A457 (-(33 * (46 * (64000000 + (r.val : ZMod 457)) + 21))) = true →
      (274739353809507284569331757290903112478931206177926734910744377245347220251093014065128728706316003695764726835929400487373527985304891391).testBit r.val = true := by decide

theorem even22_b21_s4_map_457 (i : ℕ)
    (h : even22A457 (-(33 * (46 * (64000000 + (i : ZMod 457)) + 21))) = true) :
    (274739353809507284569331757290903112478931206177926734910744377245347220251093014065128728706316003695764726835929400487373527985304891391).testBit (i % 457) = true := by
  let r : Fin 457 := ⟨i % 457, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_457_fin r
  change even22A457
    (-(33 * (46 * (64000000 + ((i % 457 : ℕ) : ZMod 457)) + 21))) = true
  have hcast : (i : ZMod 457) = ((i % 457 : ℕ) : ZMod 457) :=
    (ZMod.natCast_mod i 457).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_461_fin : ∀ r : Fin 461,
    even22A461 (-(33 * (46 * (64000000 + (r.val : ZMod 461)) + 21))) = true →
      (2788153257672475347422369586697843774018925777181396735931215301572490433955419058653850135259490139167797205142100629391499542818706817021).testBit r.val = true := by decide

theorem even22_b21_s4_map_461 (i : ℕ)
    (h : even22A461 (-(33 * (46 * (64000000 + (i : ZMod 461)) + 21))) = true) :
    (2788153257672475347422369586697843774018925777181396735931215301572490433955419058653850135259490139167797205142100629391499542818706817021).testBit (i % 461) = true := by
  let r : Fin 461 := ⟨i % 461, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_461_fin r
  change even22A461
    (-(33 * (46 * (64000000 + ((i % 461 : ℕ) : ZMod 461)) + 21))) = true
  have hcast : (i : ZMod 461) = ((i % 461 : ℕ) : ZMod 461) :=
    (ZMod.natCast_mod i 461).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_463_fin : ∀ r : Fin 463,
    even22A463 (-(33 * (46 * (64000000 + (r.val : ZMod 463)) + 21))) = true →
      (23817049896548889191305000000018158681332274209058830513607828680115823222814699098452734265163737514898926308905408025817491821614409318319).testBit r.val = true := by decide

theorem even22_b21_s4_map_463 (i : ℕ)
    (h : even22A463 (-(33 * (46 * (64000000 + (i : ZMod 463)) + 21))) = true) :
    (23817049896548889191305000000018158681332274209058830513607828680115823222814699098452734265163737514898926308905408025817491821614409318319).testBit (i % 463) = true := by
  let r : Fin 463 := ⟨i % 463, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_463_fin r
  change even22A463
    (-(33 * (46 * (64000000 + ((i % 463 : ℕ) : ZMod 463)) + 21))) = true
  have hcast : (i : ZMod 463) = ((i % 463 : ℕ) : ZMod 463) :=
    (ZMod.natCast_mod i 463).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_467_fin : ∀ r : Fin 467,
    even22A467 (-(33 * (46 * (64000000 + (r.val : ZMod 467)) + 21))) = true →
      (273849549739117355411473345128458665156494427555148220511230818791335893190935651021485767593652336264399551133366442415789789905646893640653).testBit r.val = true := by decide

theorem even22_b21_s4_map_467 (i : ℕ)
    (h : even22A467 (-(33 * (46 * (64000000 + (i : ZMod 467)) + 21))) = true) :
    (273849549739117355411473345128458665156494427555148220511230818791335893190935651021485767593652336264399551133366442415789789905646893640653).testBit (i % 467) = true := by
  let r : Fin 467 := ⟨i % 467, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_467_fin r
  change even22A467
    (-(33 * (46 * (64000000 + ((i % 467 : ℕ) : ZMod 467)) + 21))) = true
  have hcast : (i : ZMod 467) = ((i % 467 : ℕ) : ZMod 467) :=
    (ZMod.natCast_mod i 467).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_479_fin : ∀ r : Fin 479,
    even22A479 (-(33 * (46 * (64000000 + (r.val : ZMod 479)) + 21))) = true →
      (777336407420909631274217204188690231038081131850971687727614565999892104852941612215400671494950580208649408509698998346306980755192157011689435).testBit r.val = true := by decide

theorem even22_b21_s4_map_479 (i : ℕ)
    (h : even22A479 (-(33 * (46 * (64000000 + (i : ZMod 479)) + 21))) = true) :
    (777336407420909631274217204188690231038081131850971687727614565999892104852941612215400671494950580208649408509698998346306980755192157011689435).testBit (i % 479) = true := by
  let r : Fin 479 := ⟨i % 479, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_479_fin r
  change even22A479
    (-(33 * (46 * (64000000 + ((i % 479 : ℕ) : ZMod 479)) + 21))) = true
  have hcast : (i : ZMod 479) = ((i % 479 : ℕ) : ZMod 479) :=
    (ZMod.natCast_mod i 479).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_487_fin : ∀ r : Fin 487,
    even22A487 (-(33 * (46 * (64000000 + (r.val : ZMod 487)) + 21))) = true →
      (199788808026352577020724444359597305865066348811450156385580515693599098719695324798461467399464642592333764558360385930212685252336442221885652735).testBit r.val = true := by decide

theorem even22_b21_s4_map_487 (i : ℕ)
    (h : even22A487 (-(33 * (46 * (64000000 + (i : ZMod 487)) + 21))) = true) :
    (199788808026352577020724444359597305865066348811450156385580515693599098719695324798461467399464642592333764558360385930212685252336442221885652735).testBit (i % 487) = true := by
  let r : Fin 487 := ⟨i % 487, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_487_fin r
  change even22A487
    (-(33 * (46 * (64000000 + ((i % 487 : ℕ) : ZMod 487)) + 21))) = true
  have hcast : (i : ZMod 487) = ((i % 487 : ℕ) : ZMod 487) :=
    (ZMod.natCast_mod i 487).symm
  rw [← hcast]
  exact h


theorem even22_b21_s4_map_491_fin : ∀ r : Fin 491,
    even22A491 (-(33 * (46 * (64000000 + (r.val : ZMod 491)) + 21))) = true →
      (4591695312505003929320997791110958687223354541253596516292498797746883066416002615765196003544445976073579684987386050276517833266818011524939874253).testBit r.val = true := by decide

theorem even22_b21_s4_map_491 (i : ℕ)
    (h : even22A491 (-(33 * (46 * (64000000 + (i : ZMod 491)) + 21))) = true) :
    (4591695312505003929320997791110958687223354541253596516292498797746883066416002615765196003544445976073579684987386050276517833266818011524939874253).testBit (i % 491) = true := by
  let r : Fin 491 := ⟨i % 491, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s4_map_491_fin r
  change even22A491
    (-(33 * (46 * (64000000 + ((i % 491 : ℕ) : ZMod 491)) + 21))) = true
  have hcast : (i : ZMod 491) = ((i % 491 : ℕ) : ZMod 491) :=
    (ZMod.natCast_mod i 491).symm
  rw [← hcast]
  exact h

def even22PackedB21S4Group7Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 449 1452257645992939249714005721511409964532055414628489609883584168474624851865866668718498687364566304105704408805114547490652791158865911) (.leaf 457 274739353809507284569331757290903112478931206177926734910744377245347220251093014065128728706316003695764726835929400487373527985304891391)) (.node (.leaf 461 2788153257672475347422369586697843774018925777181396735931215301572490433955419058653850135259490139167797205142100629391499542818706817021) (.leaf 463 23817049896548889191305000000018158681332274209058830513607828680115823222814699098452734265163737514898926308905408025817491821614409318319))) (.node (.node (.leaf 467 273849549739117355411473345128458665156494427555148220511230818791335893190935651021485767593652336264399551133366442415789789905646893640653) (.leaf 479 777336407420909631274217204188690231038081131850971687727614565999892104852941612215400671494950580208649408509698998346306980755192157011689435)) (.node (.leaf 487 199788808026352577020724444359597305865066348811450156385580515693599098719695324798461467399464642592333764558360385930212685252336442221885652735) (.leaf 491 4591695312505003929320997791110958687223354541253596516292498797746883066416002615765196003544445976073579684987386050276517833266818011524939874253))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S4Group7TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (64000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S4Group7Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_449 i
          have hA := even22_allowed_int even22A449 even22_allowed_449 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_457 i
          have hA := even22_allowed_int even22A457 even22_allowed_457 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_461 i
          have hA := even22_allowed_int even22A461 even22_allowed_461 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_463 i
          have hA := even22_allowed_int even22A463 even22_allowed_463 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_467 i
          have hA := even22_allowed_int even22A467 even22_allowed_467 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_479 i
          have hA := even22_allowed_int even22A479 even22_allowed_479 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_487 i
          have hA := even22_allowed_int even22A487 even22_allowed_487 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s4_map_491 i
          have hA := even22_allowed_int even22A491 even22_allowed_491 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
