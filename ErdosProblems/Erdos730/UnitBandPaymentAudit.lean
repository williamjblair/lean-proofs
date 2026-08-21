/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.UnitBandPayment

/-!
Independent kernel-surface and strict-boundary audit for the full unit band.
-/

namespace Erdos730

/-- Exact positive-`r` characterization of the paid strict band. -/
theorem audit_unitBandEnvelope_iff
    {a r : ℕ} (hr : 1 ≤ r) :
    UnitBandEnvelope a r ↔ r + 1 ≤ a := by
  unfold UnitBandEnvelope
  omega

/-- Exact positive-`r` characterization of the unpaid complementary band. -/
theorem audit_unitBand_complement_iff
    {a r : ℕ} (hr : 1 ≤ r) :
    ¬ UnitBandEnvelope a r ↔ a ≤ r := by
  rw [audit_unitBandEnvelope_iff hr]
  omega

/-- The same complement stated directly in terms of the natural slack. -/
theorem audit_unitBand_slack_ge_iff
    {a r : ℕ} (hr : 1 ≤ r) :
    r ≤ 2 * r - a ↔ a ≤ r := by
  omega

#print axioms unitBandEnvelope_forces_high_exponent
#print axioms unitBandEnvelope_prime_power_clearance
#print axioms cutoff_lt_of_unitBand_maximal
#print axioms unitBandDyadicThresholdBase_strictMono_step
#print axioms unitBand_endpoint_threshold_certificate
#print axioms unitBand_endpoint_sqrt_floor_certificate
#print axioms unitBand_endpoint_cuberoot_floor_certificate
#print axioms unitBand_endpoint_payment_identity
#print axioms unitBand_endpoint_payment_lt_one_percent
#print axioms unitBand_endpoint_payment_margin
#print axioms audit_unitBandEnvelope_iff
#print axioms audit_unitBand_complement_iff
#print axioms audit_unitBand_slack_ge_iff

end Erdos730
