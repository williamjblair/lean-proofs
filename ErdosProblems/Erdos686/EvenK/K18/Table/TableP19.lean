import ErdosProblems.Erdos686.EvenK.K18.Table.TableDefs
namespace Erdos686.Erdos686Variant

set_option maxHeartbeats 10000000 in
-- Exhaustive prime-field certificate: 19^2 center pairs.
set_option maxRecDepth 1000000 in
theorem even18_allowed_19 : ∀ w v : ZMod 19,
    evenTable18S w = 4 * evenTable18S v →
      even18A19 (evenTable18T w - 2 * evenTable18T v) = true := by decide

end Erdos686.Erdos686Variant
