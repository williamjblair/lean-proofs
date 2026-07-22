import ErdosProblems.Erdos686.EvenK.FiniteTableDefs
namespace Erdos686.Erdos686Variant
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem even24_allowed_157 : ∀ w v : ZMod 157,
    evenTable24S w = 4 * evenTable24S v →
      even24A157 (evenTable24T w - 2 * evenTable24T v) = true := by decide
end Erdos686.Erdos686Variant
