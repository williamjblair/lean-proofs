import ErdosProblems.Erdos686EvenK22PackedB29S4Maps0
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps1
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps2
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps3
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps4
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps5
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps6
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps7
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps8
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps9
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps10
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps11
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps12
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps13
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps14
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps15
import ErdosProblems.Erdos686EvenK22PackedB29S4Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB29S4Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB29S4Group0Tree even22PackedB29S4Group1Tree) (.node even22PackedB29S4Group2Tree even22PackedB29S4Group3Tree)) (.node (.node even22PackedB29S4Group4Tree even22PackedB29S4Group5Tree) (.node even22PackedB29S4Group6Tree even22PackedB29S4Group7Tree))) (.node (.node (.node even22PackedB29S4Group8Tree even22PackedB29S4Group9Tree) (.node even22PackedB29S4Group10Tree even22PackedB29S4Group11Tree)) (.node (.node even22PackedB29S4Group12Tree even22PackedB29S4Group13Tree) (.node even22PackedB29S4Group14Tree (.node even22PackedB29S4Group15Tree even22PackedB29S4Group16Tree)))))

def even22PackedB29S4Intersection : BitVec 16000000 :=
  even22PackedB29S4Tree.eval 16000000 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB29S4Intersection_zero :
    even22PackedB29S4Intersection = BitVec.zero 16000000 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b29_s4_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 64000000 ≤ q) (hhi : q < 80000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 29)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 64000000
  have hi : i < 16000000 := by dsimp [i]; omega
  have hqi : 64000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB29S4Intersection_zero
  change even22PackedB29S4Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S4Group0TreeSupports hi hS hm
        · exact even22PackedB29S4Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S4Group2TreeSupports hi hS hm
        · exact even22PackedB29S4Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S4Group4TreeSupports hi hS hm
        · exact even22PackedB29S4Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S4Group6TreeSupports hi hS hm
        · exact even22PackedB29S4Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB29S4Group8TreeSupports hi hS hm
        · exact even22PackedB29S4Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S4Group10TreeSupports hi hS hm
        · exact even22PackedB29S4Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB29S4Group12TreeSupports hi hS hm
        · exact even22PackedB29S4Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB29S4Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB29S4Group15TreeSupports hi hS hm
          · exact even22PackedB29S4Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
