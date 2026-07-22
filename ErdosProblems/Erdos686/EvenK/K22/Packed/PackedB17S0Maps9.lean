import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b17_s0_map_563_fin : ∀ r : Fin 563,
    even22A563 (-(33 * (46 * (0 + (r.val : ZMod 563)) + 17))) = true →
      (22643306591595601551200711683877135531754771383942065938502599095148066098117130205831663208940533179816437626888746217108802287921402924693393926407994333167379151847253).testBit r.val = true := by decide

theorem even22_b17_s0_map_563 (i : ℕ)
    (h : even22A563 (-(33 * (46 * (0 + (i : ZMod 563)) + 17))) = true) :
    (22643306591595601551200711683877135531754771383942065938502599095148066098117130205831663208940533179816437626888746217108802287921402924693393926407994333167379151847253).testBit (i % 563) = true := by
  let r : Fin 563 := ⟨i % 563, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_563_fin r
  change even22A563
    (-(33 * (46 * (0 + ((i % 563 : ℕ) : ZMod 563)) + 17))) = true
  have hcast : (i : ZMod 563) = ((i % 563 : ℕ) : ZMod 563) :=
    (ZMod.natCast_mod i 563).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_569_fin : ∀ r : Fin 569,
    even22A569 (-(33 * (46 * (0 + (r.val : ZMod 569)) + 17))) = true →
      (1871877977273510502255973006757261707439588186245002250942604946516243828281630863112903651267162556011913970652765109085078635184547807968206130081748656420361021488365503).testBit r.val = true := by decide

theorem even22_b17_s0_map_569 (i : ℕ)
    (h : even22A569 (-(33 * (46 * (0 + (i : ZMod 569)) + 17))) = true) :
    (1871877977273510502255973006757261707439588186245002250942604946516243828281630863112903651267162556011913970652765109085078635184547807968206130081748656420361021488365503).testBit (i % 569) = true := by
  let r : Fin 569 := ⟨i % 569, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_569_fin r
  change even22A569
    (-(33 * (46 * (0 + ((i % 569 : ℕ) : ZMod 569)) + 17))) = true
  have hcast : (i : ZMod 569) = ((i % 569 : ℕ) : ZMod 569) :=
    (ZMod.natCast_mod i 569).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_571_fin : ∀ r : Fin 571,
    even22A571 (-(33 * (46 * (0 + (r.val : ZMod 571)) + 17))) = true →
      (7649758717039128326757731190412906195245918902130864908977450734799767570850613449959372564110949189616881545577093626014436528164020755600236308612540767578686493977993150).testBit r.val = true := by decide

theorem even22_b17_s0_map_571 (i : ℕ)
    (h : even22A571 (-(33 * (46 * (0 + (i : ZMod 571)) + 17))) = true) :
    (7649758717039128326757731190412906195245918902130864908977450734799767570850613449959372564110949189616881545577093626014436528164020755600236308612540767578686493977993150).testBit (i % 571) = true := by
  let r : Fin 571 := ⟨i % 571, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_571_fin r
  change even22A571
    (-(33 * (46 * (0 + ((i % 571 : ℕ) : ZMod 571)) + 17))) = true
  have hcast : (i : ZMod 571) = ((i % 571 : ℕ) : ZMod 571) :=
    (ZMod.natCast_mod i 571).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_577_fin : ∀ r : Fin 577,
    even22A577 (-(33 * (46 * (0 + (r.val : ZMod 577)) + 17))) = true →
      (485722172883577347184440704923745266965613855692291517679442901364517230350504171247569523781436815068428117319501743341955353330096061569499362444047834112479101952734526847).testBit r.val = true := by decide

theorem even22_b17_s0_map_577 (i : ℕ)
    (h : even22A577 (-(33 * (46 * (0 + (i : ZMod 577)) + 17))) = true) :
    (485722172883577347184440704923745266965613855692291517679442901364517230350504171247569523781436815068428117319501743341955353330096061569499362444047834112479101952734526847).testBit (i % 577) = true := by
  let r : Fin 577 := ⟨i % 577, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_577_fin r
  change even22A577
    (-(33 * (46 * (0 + ((i % 577 : ℕ) : ZMod 577)) + 17))) = true
  have hcast : (i : ZMod 577) = ((i % 577 : ℕ) : ZMod 577) :=
    (ZMod.natCast_mod i 577).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_587_fin : ∀ r : Fin 587,
    even22A587 (-(33 * (46 * (0 + (r.val : ZMod 587)) + 17))) = true →
      (490698444287637232936981743593411156230780163197229977421357217370791522826929361518490979619523623485078444425808175396564674044957066815279589348844590492039678239209504636795).testBit r.val = true := by decide

theorem even22_b17_s0_map_587 (i : ℕ)
    (h : even22A587 (-(33 * (46 * (0 + (i : ZMod 587)) + 17))) = true) :
    (490698444287637232936981743593411156230780163197229977421357217370791522826929361518490979619523623485078444425808175396564674044957066815279589348844590492039678239209504636795).testBit (i % 587) = true := by
  let r : Fin 587 := ⟨i % 587, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_587_fin r
  change even22A587
    (-(33 * (46 * (0 + ((i % 587 : ℕ) : ZMod 587)) + 17))) = true
  have hcast : (i : ZMod 587) = ((i % 587 : ℕ) : ZMod 587) :=
    (ZMod.natCast_mod i 587).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_593_fin : ∀ r : Fin 593,
    even22A593 (-(33 * (46 * (0 + (r.val : ZMod 593)) + 17))) = true →
      (21780811243329789644295837761645527234006232301172191874699400820476595816430653195254136343930772672219588428505707881085765184257098748358675855670872779368348622719816797222511).testBit r.val = true := by decide

theorem even22_b17_s0_map_593 (i : ℕ)
    (h : even22A593 (-(33 * (46 * (0 + (i : ZMod 593)) + 17))) = true) :
    (21780811243329789644295837761645527234006232301172191874699400820476595816430653195254136343930772672219588428505707881085765184257098748358675855670872779368348622719816797222511).testBit (i % 593) = true := by
  let r : Fin 593 := ⟨i % 593, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_593_fin r
  change even22A593
    (-(33 * (46 * (0 + ((i % 593 : ℕ) : ZMod 593)) + 17))) = true
  have hcast : (i : ZMod 593) = ((i % 593 : ℕ) : ZMod 593) :=
    (ZMod.natCast_mod i 593).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_599_fin : ∀ r : Fin 599,
    even22A599 (-(33 * (46 * (0 + (r.val : ZMod 599)) + 17))) = true →
      (2042086381259645730768360009108028505501655468869976672789973611162574297844664081405720687756047529091533843886139604721494096369222136930820620475366213665862941221933326698020863).testBit r.val = true := by decide

theorem even22_b17_s0_map_599 (i : ℕ)
    (h : even22A599 (-(33 * (46 * (0 + (i : ZMod 599)) + 17))) = true) :
    (2042086381259645730768360009108028505501655468869976672789973611162574297844664081405720687756047529091533843886139604721494096369222136930820620475366213665862941221933326698020863).testBit (i % 599) = true := by
  let r : Fin 599 := ⟨i % 599, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_599_fin r
  change even22A599
    (-(33 * (46 * (0 + ((i % 599 : ℕ) : ZMod 599)) + 17))) = true
  have hcast : (i : ZMod 599) = ((i % 599 : ℕ) : ZMod 599) :=
    (ZMod.natCast_mod i 599).symm
  rw [← hcast]
  exact h


theorem even22_b17_s0_map_601_fin : ∀ r : Fin 601,
    even22A601 (-(33 * (46 * (0 + (r.val : ZMod 601)) + 17))) = true →
      (8286802333257769268656915558571116096512246037317767072729515501516574607966799323343563585315454108383596986259707539776405274549012410760924490003848761098149140306860357697003455).testBit r.val = true := by decide

theorem even22_b17_s0_map_601 (i : ℕ)
    (h : even22A601 (-(33 * (46 * (0 + (i : ZMod 601)) + 17))) = true) :
    (8286802333257769268656915558571116096512246037317767072729515501516574607966799323343563585315454108383596986259707539776405274549012410760924490003848761098149140306860357697003455).testBit (i % 601) = true := by
  let r : Fin 601 := ⟨i % 601, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b17_s0_map_601_fin r
  change even22A601
    (-(33 * (46 * (0 + ((i % 601 : ℕ) : ZMod 601)) + 17))) = true
  have hcast : (i : ZMod 601) = ((i % 601 : ℕ) : ZMod 601) :=
    (ZMod.natCast_mod i 601).symm
  rw [← hcast]
  exact h

def even22PackedB17S0Group9Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 563 22643306591595601551200711683877135531754771383942065938502599095148066098117130205831663208940533179816437626888746217108802287921402924693393926407994333167379151847253) (.leaf 569 1871877977273510502255973006757261707439588186245002250942604946516243828281630863112903651267162556011913970652765109085078635184547807968206130081748656420361021488365503)) (.node (.leaf 571 7649758717039128326757731190412906195245918902130864908977450734799767570850613449959372564110949189616881545577093626014436528164020755600236308612540767578686493977993150) (.leaf 577 485722172883577347184440704923745266965613855692291517679442901364517230350504171247569523781436815068428117319501743341955353330096061569499362444047834112479101952734526847))) (.node (.node (.leaf 587 490698444287637232936981743593411156230780163197229977421357217370791522826929361518490979619523623485078444425808175396564674044957066815279589348844590492039678239209504636795) (.leaf 593 21780811243329789644295837761645527234006232301172191874699400820476595816430653195254136343930772672219588428505707881085765184257098748358675855670872779368348622719816797222511)) (.node (.leaf 599 2042086381259645730768360009108028505501655468869976672789973611162574297844664081405720687756047529091533843886139604721494096369222136930820620475366213665862941221933326698020863) (.leaf 601 8286802333257769268656915558571116096512246037317767072729515501516574607966799323343563585315454108383596986259707539776405274549012410760924490003848761098149140306860357697003455))))

set_option maxRecDepth 10000 in
theorem even22PackedB17S0Group9TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (0 + (i : ℤ)) + 17)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB17S0Group9Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_563 i
          have hA := even22_allowed_int even22A563 even22_allowed_563 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_569 i
          have hA := even22_allowed_int even22A569 even22_allowed_569 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_571 i
          have hA := even22_allowed_int even22A571 even22_allowed_571 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_577 i
          have hA := even22_allowed_int even22A577 even22_allowed_577 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_587 i
          have hA := even22_allowed_int even22A587 even22_allowed_587 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_593 i
          have hA := even22_allowed_int even22A593 even22_allowed_593 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_599 i
          have hA := even22_allowed_int even22A599 even22_allowed_599 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b17_s0_map_601 i
          have hA := even22_allowed_int even22A601 even22_allowed_601 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
