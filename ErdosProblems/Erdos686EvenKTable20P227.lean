import ErdosProblems.Erdos686EvenKFiniteTableDefs
namespace Erdos686.Erdos686Variant
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem even20_allowed_227 : ∀ w v : ZMod 227,
    evenTable20S w = 4 * evenTable20S v →
      even20A227 (evenTable20T w - 2 * evenTable20T v) = true := by decide
end Erdos686.Erdos686Variant
