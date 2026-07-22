import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps0
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps1
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps2
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps3
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps4
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps5
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps6
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps7
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps8
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps9
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps10
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps11
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps12
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps13
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps14
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps15
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedB25S3Maps16

namespace Erdos686.Erdos686Variant

set_option maxRecDepth 10000

def even22PackedB25S3Tree : Even22PeriodicTree :=
  (.node (.node (.node (.node even22PackedB25S3Group0Tree even22PackedB25S3Group1Tree) (.node even22PackedB25S3Group2Tree even22PackedB25S3Group3Tree)) (.node (.node even22PackedB25S3Group4Tree even22PackedB25S3Group5Tree) (.node even22PackedB25S3Group6Tree even22PackedB25S3Group7Tree))) (.node (.node (.node even22PackedB25S3Group8Tree even22PackedB25S3Group9Tree) (.node even22PackedB25S3Group10Tree even22PackedB25S3Group11Tree)) (.node (.node even22PackedB25S3Group12Tree even22PackedB25S3Group13Tree) (.node even22PackedB25S3Group14Tree (.node even22PackedB25S3Group15Tree even22PackedB25S3Group16Tree)))))

def even22PackedB25S3Intersection : BitVec 16000000 :=
  even22PackedB25S3Tree.eval 16000000 18

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
theorem even22PackedB25S3Intersection_zero :
    even22PackedB25S3Intersection = BitVec.zero 16000000 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem even22_packed_b25_s3_no_centers
    {w v : ℤ} {q : ℕ}
    (hlo : 48000000 ≤ q) (hhi : q < 64000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (q : ℤ) + 25)) =
      evenTable22T w - 2 * evenTable22T v) : False := by
  let i := q - 48000000
  have hi : i < 16000000 := by dsimp [i]; omega
  have hqi : 48000000 + i = q := by dsimp [i]; omega
  rw [← hqi] at hm
  apply even22No_index_of_tree_zero hi even22PackedB25S3Intersection_zero
  change even22PackedB25S3Tree.Supports i 18
  constructor
  · constructor
    · constructor
      · constructor
        · exact even22PackedB25S3Group0TreeSupports hi hS hm
        · exact even22PackedB25S3Group1TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S3Group2TreeSupports hi hS hm
        · exact even22PackedB25S3Group3TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB25S3Group4TreeSupports hi hS hm
        · exact even22PackedB25S3Group5TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S3Group6TreeSupports hi hS hm
        · exact even22PackedB25S3Group7TreeSupports hi hS hm
  · constructor
    · constructor
      · constructor
        · exact even22PackedB25S3Group8TreeSupports hi hS hm
        · exact even22PackedB25S3Group9TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S3Group10TreeSupports hi hS hm
        · exact even22PackedB25S3Group11TreeSupports hi hS hm
    · constructor
      · constructor
        · exact even22PackedB25S3Group12TreeSupports hi hS hm
        · exact even22PackedB25S3Group13TreeSupports hi hS hm
      · constructor
        · exact even22PackedB25S3Group14TreeSupports hi hS hm
        · constructor
          · exact even22PackedB25S3Group15TreeSupports hi hS hm
          · exact even22PackedB25S3Group16TreeSupports hi hS hm
end Erdos686.Erdos686Variant
