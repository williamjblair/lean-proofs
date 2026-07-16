import ErdosProblems.Erdos686EvenK22PackedB29S5Maps0
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps1
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps2
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps3
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps4
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps5
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps6
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps7
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps8
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps9
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps10
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps11
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps12
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps13
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps14
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps15
import ErdosProblems.Erdos686EvenK22PackedB29S5Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB29S5Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB29S5Group0Tree even22PackedB29S5Group1Tree) (.node even22PackedB29S5Group2Tree even22PackedB29S5Group3Tree)) (.node (.node even22PackedB29S5Group4Tree even22PackedB29S5Group5Tree) (.node even22PackedB29S5Group6Tree even22PackedB29S5Group7Tree))) (.node (.node (.node even22PackedB29S5Group8Tree even22PackedB29S5Group9Tree) (.node even22PackedB29S5Group10Tree even22PackedB29S5Group11Tree)) (.node (.node even22PackedB29S5Group12Tree even22PackedB29S5Group13Tree) (.node even22PackedB29S5Group14Tree (.node even22PackedB29S5Group15Tree even22PackedB29S5Group16Tree)))))

def even22PackedB29S5Intersection : BitVec 2503185 :=
  even22PackedB29S5Tree.eval 2503185 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB29S5Intersection_zero :
    even22PackedB29S5Intersection = BitVec.zero 2503185 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b29_s5_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 80000000 ≤ q) (hhi : q < 82503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 29)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 80000000
  have hi : i < 2503185 := by dsimp [i]; omega
  have hqi : 80000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB29S5Intersection_zero
  change even22PackedB29S5Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S5Group0TreeSupports hi hS hm
        · exact even22PackedB29S5Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S5Group2TreeSupports hi hS hm
        · exact even22PackedB29S5Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S5Group4TreeSupports hi hS hm
        · exact even22PackedB29S5Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S5Group6TreeSupports hi hS hm
        · exact even22PackedB29S5Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S5Group8TreeSupports hi hS hm
        · exact even22PackedB29S5Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S5Group10TreeSupports hi hS hm
        · exact even22PackedB29S5Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S5Group12TreeSupports hi hS hm
        · exact even22PackedB29S5Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S5Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB29S5Group15TreeSupports hi hS hm
          · exact even22PackedB29S5Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
