import Research.RademacherBallot
import Research.Reduction

namespace Erdos521

/-- After the fully unconditional cone-record recurrence theorem, the published local strong law
is the sole remaining input needed to refute the Erdős--521 claim. -/
theorem erdos_521_negative_of_localStrongLaw (hlocal : LocalStrongLaw) : ¬ Claim :=
  negative_of_localStrongLaw_of_coneRecords hlocal positive_infinitelyOftenConeRecords

end Erdos521
