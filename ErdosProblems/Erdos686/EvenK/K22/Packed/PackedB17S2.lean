import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps0
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps1
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps2
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps3
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps4
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps5
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps6
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps7
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps8
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps9
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps10
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps11
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps12
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps13
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps14
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps15
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB17S2Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB17S2Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB17S2Group0Tree even22PackedB17S2Group1Tree) (.node even22PackedB17S2Group2Tree even22PackedB17S2Group3Tree)) (.node (.node even22PackedB17S2Group4Tree even22PackedB17S2Group5Tree) (.node even22PackedB17S2Group6Tree even22PackedB17S2Group7Tree))) (.node (.node (.node even22PackedB17S2Group8Tree even22PackedB17S2Group9Tree) (.node even22PackedB17S2Group10Tree even22PackedB17S2Group11Tree)) (.node (.node even22PackedB17S2Group12Tree even22PackedB17S2Group13Tree) (.node even22PackedB17S2Group14Tree (.node even22PackedB17S2Group15Tree even22PackedB17S2Group16Tree)))))

def even22PackedB17S2Intersection : BitVec 16000000 :=
  even22PackedB17S2Tree.eval 16000000 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB17S2Intersection_zero :
    even22PackedB17S2Intersection = BitVec.zero 16000000 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b17_s2_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 32000000 ≤ q) (hhi : q < 48000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 17)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 32000000
  have hi : i < 16000000 := by dsimp [i]; omega
  have hqi : 32000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB17S2Intersection_zero
  change even22PackedB17S2Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB17S2Group0TreeSupports hi hS hm
        · exact even22PackedB17S2Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S2Group2TreeSupports hi hS hm
        · exact even22PackedB17S2Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB17S2Group4TreeSupports hi hS hm
        · exact even22PackedB17S2Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S2Group6TreeSupports hi hS hm
        · exact even22PackedB17S2Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB17S2Group8TreeSupports hi hS hm
        · exact even22PackedB17S2Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S2Group10TreeSupports hi hS hm
        · exact even22PackedB17S2Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB17S2Group12TreeSupports hi hS hm
        · exact even22PackedB17S2Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB17S2Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB17S2Group15TreeSupports hi hS hm
          · exact even22PackedB17S2Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
