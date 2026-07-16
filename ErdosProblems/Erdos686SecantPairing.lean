/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686NormalizedMatching

/-!
# Erdős 686: two-owner secants and controlled pairing

This module begins the direct large-`k` matching audit.  It first isolates the
exact arithmetic common to any two coprime row-diagonal owners.  Later
sections will add the zero-secant geometry and an explicit controlled pairing
algorithm.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The signed secant determinant of two row-diagonal owner points, evaluated
against the translated point `(-n,-d)`. -/
def twoOwnerSecantForm
    (n d j₁ j₂ ρ₁ ρ₂ : ℤ) : ℤ :=
  (ρ₂ - ρ₁) * (n + j₁) - (j₂ - j₁) * (d + ρ₁)

/-- Re-expanding the same secant determinant at the second owner leaves it
unchanged. -/
theorem twoOwnerSecantForm_recenter
    (n d j₁ j₂ ρ₁ ρ₂ : ℤ) :
    twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ =
      (ρ₂ - ρ₁) * (n + j₂) - (j₂ - j₁) * (d + ρ₂) := by
  simp only [twoOwnerSecantForm]
  ring

/-- Two coprime owner moduli divide their common secant determinant as a
product.  This is the exact two-owner secant divisor, stated over `ℤ` so that
signed offsets need no truncated subtraction. -/
theorem two_owner_secant_dvd
    {P₁ P₂ : ℕ} {n d j₁ j₂ ρ₁ ρ₂ : ℤ}
    (hcop : P₁.Coprime P₂)
    (h₁row : (P₁ : ℤ) ∣ n + j₁)
    (h₁diag : (P₁ : ℤ) ∣ d + ρ₁)
    (h₂row : (P₂ : ℤ) ∣ n + j₂)
    (h₂diag : (P₂ : ℤ) ∣ d + ρ₂) :
    ((P₁ * P₂ : ℕ) : ℤ) ∣
      twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
  have h₁ :
      (P₁ : ℤ) ∣ twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
    exact dvd_sub
      (dvd_mul_of_dvd_right h₁row (ρ₂ - ρ₁))
      (dvd_mul_of_dvd_right h₁diag (j₂ - j₁))
  have h₂ :
      (P₂ : ℤ) ∣ twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
    rw [twoOwnerSecantForm_recenter]
    exact dvd_sub
      (dvd_mul_of_dvd_right h₂row (ρ₂ - ρ₁))
      (dvd_mul_of_dvd_right h₂diag (j₂ - j₁))
  have hcopZ : IsCoprime (P₁ : ℤ) (P₂ : ℤ) := hcop.isCoprime
  simpa using hcopZ.mul_dvd h₁ h₂

#print axioms twoOwnerSecantForm_recenter
#print axioms two_owner_secant_dvd

end Erdos686Variant
end Erdos686
