import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps0
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps1
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps2
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps3
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps4
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps5
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps6
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps7
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps8
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps9
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps10
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps11
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps12
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps13
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps14
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps15
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S5Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB17S5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB17S5Group0Tree even22PackedB17S5Group1Tree) (.node even22PackedB17S5Group2Tree even22PackedB17S5Group3Tree)) (.node (.node even22PackedB17S5Group4Tree even22PackedB17S5Group5Tree) (.node even22PackedB17S5Group6Tree even22PackedB17S5Group7Tree))) (.node (.node (.node even22PackedB17S5Group8Tree even22PackedB17S5Group9Tree) (.node even22PackedB17S5Group10Tree even22PackedB17S5Group11Tree)) (.node (.node even22PackedB17S5Group12Tree even22PackedB17S5Group13Tree) (.node even22PackedB17S5Group14Tree (.node even22PackedB17S5Group15Tree even22PackedB17S5Group16Tree)))))

def even22PackedB17S5Intersection : BitVec 2503186 :=
  even22PackedB17S5Tree.eval 2503186 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB17S5Intersection_zero :
    even22PackedB17S5Intersection = BitVec.zero 2503186 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b17_s5_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 80000000 ≤ q) (hhi : q < 82503186)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 17)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 80000000
  have hi : i < 2503186 := by dsimp [i]; omega
  have hqi : 80000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB17S5Intersection_zero
  change even22PackedB17S5Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB17S5Group0TreeSupports hi hS hm
        · exact even22PackedB17S5Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S5Group2TreeSupports hi hS hm
        · exact even22PackedB17S5Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB17S5Group4TreeSupports hi hS hm
        · exact even22PackedB17S5Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S5Group6TreeSupports hi hS hm
        · exact even22PackedB17S5Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB17S5Group8TreeSupports hi hS hm
        · exact even22PackedB17S5Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S5Group10TreeSupports hi hS hm
        · exact even22PackedB17S5Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB17S5Group12TreeSupports hi hS hm
        · exact even22PackedB17S5Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S5Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB17S5Group15TreeSupports hi hS hm
          · exact even22PackedB17S5Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
