import ErdosProblems.Erdos686EvenK22PackedB29S1Maps0
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps1
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps2
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps3
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps4
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps5
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps6
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps7
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps8
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps9
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps10
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps11
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps12
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps13
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps14
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps15
import ErdosProblems.Erdos686EvenK22PackedB29S1Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB29S1Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB29S1Group0Tree even22PackedB29S1Group1Tree) (.node even22PackedB29S1Group2Tree even22PackedB29S1Group3Tree)) (.node (.node even22PackedB29S1Group4Tree even22PackedB29S1Group5Tree) (.node even22PackedB29S1Group6Tree even22PackedB29S1Group7Tree))) (.node (.node (.node even22PackedB29S1Group8Tree even22PackedB29S1Group9Tree) (.node even22PackedB29S1Group10Tree even22PackedB29S1Group11Tree)) (.node (.node even22PackedB29S1Group12Tree even22PackedB29S1Group13Tree) (.node even22PackedB29S1Group14Tree (.node even22PackedB29S1Group15Tree even22PackedB29S1Group16Tree)))))

def even22PackedB29S1Intersection : BitVec 16000000 :=
  even22PackedB29S1Tree.eval 16000000 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB29S1Intersection_zero :
    even22PackedB29S1Intersection = BitVec.zero 16000000 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b29_s1_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 16000000 ≤ q) (hhi : q < 32000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 29)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 16000000
  have hi : i < 16000000 := by dsimp [i]; omega
  have hqi : 16000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB29S1Intersection_zero
  change even22PackedB29S1Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S1Group0TreeSupports hi hS hm
        · exact even22PackedB29S1Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S1Group2TreeSupports hi hS hm
        · exact even22PackedB29S1Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S1Group4TreeSupports hi hS hm
        · exact even22PackedB29S1Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S1Group6TreeSupports hi hS hm
        · exact even22PackedB29S1Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S1Group8TreeSupports hi hS hm
        · exact even22PackedB29S1Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S1Group10TreeSupports hi hS hm
        · exact even22PackedB29S1Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S1Group12TreeSupports hi hS hm
        · exact even22PackedB29S1Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S1Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB29S1Group15TreeSupports hi hS hm
          · exact even22PackedB29S1Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
