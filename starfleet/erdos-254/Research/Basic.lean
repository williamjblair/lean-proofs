import Research.Statement
import Research.FinalProof

/-!
# Erdős Problem 254

The canonical statement is in `Research.Statement`. This theorem is initially
left as the unique proof goal; a final accepted solution must be fully checked
by the Lean kernel and must pass `check_answer/verify.sh`.
-/

namespace Erdos254

/-- Erdős Problem 254. -/
theorem erdos_254 : Statement :=
  FinalProof.erdos_254

end Erdos254
