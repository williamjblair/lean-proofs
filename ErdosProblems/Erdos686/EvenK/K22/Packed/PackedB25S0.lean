import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps0
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps1
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps2
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps3
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps4
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps5
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps6
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps7
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps8
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps9
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps10
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps11
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps12
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps13
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps14
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps15
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S0Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB25S0Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB25S0Group0Tree even22PackedB25S0Group1Tree) (.node even22PackedB25S0Group2Tree even22PackedB25S0Group3Tree)) (.node (.node even22PackedB25S0Group4Tree even22PackedB25S0Group5Tree) (.node even22PackedB25S0Group6Tree even22PackedB25S0Group7Tree))) (.node (.node (.node even22PackedB25S0Group8Tree even22PackedB25S0Group9Tree) (.node even22PackedB25S0Group10Tree even22PackedB25S0Group11Tree)) (.node (.node even22PackedB25S0Group12Tree even22PackedB25S0Group13Tree) (.node even22PackedB25S0Group14Tree (.node even22PackedB25S0Group15Tree even22PackedB25S0Group16Tree)))))

def even22PackedB25S0Intersection : BitVec 16000000 :=
  even22PackedB25S0Tree.eval 16000000 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB25S0Intersection_zero :
    even22PackedB25S0Intersection = BitVec.zero 16000000 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b25_s0_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 0 ≤ q) (hhi : q < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 25)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 0
  have hi : i < 16000000 := by dsimp [i]; omega
  have hqi : 0 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB25S0Intersection_zero
  change even22PackedB25S0Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB25S0Group0TreeSupports hi hS hm
        · exact even22PackedB25S0Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S0Group2TreeSupports hi hS hm
        · exact even22PackedB25S0Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB25S0Group4TreeSupports hi hS hm
        · exact even22PackedB25S0Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S0Group6TreeSupports hi hS hm
        · exact even22PackedB25S0Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB25S0Group8TreeSupports hi hS hm
        · exact even22PackedB25S0Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S0Group10TreeSupports hi hS hm
        · exact even22PackedB25S0Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB25S0Group12TreeSupports hi hS hm
        · exact even22PackedB25S0Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S0Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB25S0Group15TreeSupports hi hS hm
          · exact even22PackedB25S0Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
