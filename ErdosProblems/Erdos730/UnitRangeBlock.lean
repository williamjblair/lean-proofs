/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

/-!
# Erdős 730: exact `p^r` block algebra in the corrected range

For the branch polynomial

`G(k)=A*pa*k^2+B*k+C`,

write `k=u+P*v` with `P=p^r`.  The quadratic Taylor formula is exact, and
its remainder contains `P^2=p^(2r)`.  Thus the low `r` output digits on an
aligned `P`-block depend only on `u`; the upper-block index enters linearly
modulo `P^2`.

This file also proves the cross-multiplied arithmetic used to turn the
aligned-block cover into a normalized first-moment bound.  Digit counting
and the finite prime-sum certificate remain in the exact Python verifier.
-/

namespace Erdos730
namespace UnitRangeBlock

/-- Generic integral quadratic branch map. -/
def quadraticBranch
    (A pa B C k : ℤ) : ℤ :=
  A * pa * k ^ 2 + B * k + C

/-- Exact Taylor expansion on an aligned block. -/
theorem quadratic_block_expansion
    (A pa B C u P v : ℤ) :
    quadraticBranch A pa B C (u + P * v) =
      quadraticBranch A pa B C u +
        P * v * (2 * A * pa * u + B) +
        A * pa * P ^ 2 * v ^ 2 := by
  simp [quadraticBranch]
  ring

/-- Modulo `P^2`, an aligned block is exactly affine in its block index. -/
theorem quadratic_block_difference_dvd_sq
    (A pa B C u P v : ℤ) :
    P ^ 2 ∣
      quadraticBranch A pa B C (u + P * v) -
        quadraticBranch A pa B C u -
        P * v * (2 * A * pa * u + B) := by
  refine ⟨A * pa * v ^ 2, ?_⟩
  rw [quadratic_block_expansion]
  ring

/-- Cross-multiplied form of the family-normalized aligned-block estimate.

`C` is an obstruction count, `P=p^r`, `M=(H-1)H^(r-1)`, `q=p^a`, and
`N` is the number of parameters in one root class below the family cutoff
`X`.  The hypotheses say:

* critical length gives `4P<=N` in the subrange `2<=a<=r`;
* one residue class has `q(N-1)<=X`;
* covering by aligned blocks gives `C*P<=M(N+2P)`.

The conclusion is exactly `C/X <= 2M/(qP)` with all division cleared. -/
theorem normalized_block_cover_cross_bound
    {C q P M N X : ℕ}
    (hP : 1 ≤ P)
    (hcritical : 4 * P ≤ N)
    (hclass : q * (N - 1) ≤ X)
    (hcount : C * P ≤ M * (N + 2 * P)) :
    C * q * P ≤ 2 * M * X := by
  have hcover : N + 2 * P ≤ 2 * (N - 1) := by
    omega
  have hqcover : q * (N + 2 * P) ≤ q * (2 * (N - 1)) :=
    Nat.mul_le_mul_left q hcover
  have hqX : q * (2 * (N - 1)) ≤ 2 * X := by
    calc
      q * (2 * (N - 1)) = 2 * (q * (N - 1)) := by ring
      _ ≤ 2 * X := Nat.mul_le_mul_left 2 hclass
  calc
    C * q * P = q * (C * P) := by ring
    _ ≤ q * (M * (N + 2 * P)) := Nat.mul_le_mul_left q hcount
    _ = M * (q * (N + 2 * P)) := by ring
    _ ≤ M * (2 * X) := Nat.mul_le_mul_left M (le_trans hqcover hqX)
    _ = 2 * M * X := by ring

/-- The rational ceiling used for all four higher-prime-power branches
leaves a positive margin below one half. -/
theorem higher_prime_power_payment_ceiling_lt_half :
    (58 : ℚ) / 125 < 1 / 2 := by
  norm_num

#print axioms quadratic_block_expansion
#print axioms quadratic_block_difference_dvd_sq
#print axioms normalized_block_cover_cross_bound
#print axioms higher_prime_power_payment_ceiling_lt_half

end UnitRangeBlock
end Erdos730
