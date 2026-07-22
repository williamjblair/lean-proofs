import ErdosProblems.Erdos686.EvenK.FiniteTableDefs
namespace Erdos686.Erdos686Variant
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem even20_allowed_239 : ∀ w v : ZMod 239,
    evenTable20S w = 4 * evenTable20S v →
      even20A239 (evenTable20T w - 2 * evenTable20T v) = true := by decide
end Erdos686.Erdos686Variant
