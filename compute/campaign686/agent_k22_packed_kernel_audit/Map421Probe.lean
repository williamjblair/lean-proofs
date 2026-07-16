import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

private theorem map421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (80000000 + (r.val : ZMod 421)) + 17))) = true →
      (4643133174891631200068741090075886305059544678285686182249245859751804735203813506257333286917800699067978013723565758192025578).testBit r.val = true := by
  decide

theorem map421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (80000000 + (i : ZMod 421)) + 17))) = true) :
    (4643133174891631200068741090075886305059544678285686182249245859751804735203813506257333286917800699067978013723565758192025578).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply map421_fin r
  change even22A421
    (-(33 * (46 * (80000000 + ((i % 421 : ℕ) : ZMod 421)) + 17))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h

end Erdos686.Erdos686Variant
